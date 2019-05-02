/* delkey.c - delete keys
 * Copyright (C) 1998, 1999, 2000, 2001, 2002, 2004,
 *               2005, 2006 Free Software Foundation, Inc.
 * Copyright (C) 2014, 2019 Werner Koch
 *
 * This file is part of GnuPG.
 *
 * GnuPG is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * GnuPG is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, see <https://www.gnu.org/licenses/>.
 */

#include <config.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <ctype.h>

#include "gpg.h"
#include "options.h"
#include "packet.h"
#include "../common/status.h"
#include "../common/iobuf.h"
#include "keydb.h"
#include "../common/util.h"
#include "main.h"
#include "trustdb.h"
#include "filter.h"
#include "../common/ttyio.h"
#include "../common/i18n.h"
#include "call-agent.h"

static gpg_error_t
agent_delete_secret_key (ctrl_t ctrl, PKT_public_key *pk)
{
  gpg_error_t err;
  char *prompt;
  char *hexgrip;

  if (agent_probe_secret_key (NULL, pk))
    return gpg_error (GPG_ERR_NO_SECKEY);

  prompt = gpg_format_keydesc (ctrl, pk, FORMAT_KEYDESC_DELKEY, 1);

  err = hexkeygrip_from_pk (pk, &hexgrip);

  /* NB: We require --yes to advise the agent not to request a confirmation.
   * The rationale for this extra pre-caution is that since 2.1 the secret key
   * may also be used for other protocols and thus deleting it from the gpg
   * would also delete the key for other tools. */
  if (!err && !opt.dry_run)
    err = agent_delete_key (NULL, hexgrip, prompt, opt.answer_yes);

  xfree (prompt);
  xfree (hexgrip);

  return err;
}

static int
confirm_deletion(ctrl_t ctrl, PACKET *pkt, int secret, int fingerprint)
{
  int yes = 0;

  if (opt.batch)
    {
      if (secret)
        return fingerprint;
      else
        return opt.answer_yes || fingerprint;
    }

  print_key_info (ctrl, NULL, 0, pkt->pkt.public_key, secret);
  tty_printf( "\n" );

  yes = cpr_get_answer_is_yes (secret? "delete_key.secret.okay": "delete_key.okay",
                               _("Delete this key from the keyring? (y/N) "));

  if (!cpr_enabled() && secret)
    {
      /* I think it is not required to check a passphrase; if the
       * user is so stupid as to let others access his secret
       * keyring (and has no backup) - it is up him to read some
       * very basic texts about security.  */
      if (yes)
        yes = cpr_get_answer_is_yes ("delete_key.secret.okay",
                                     _("This is a secret key! - really delete? (y/N) "));

      /* Extra confirmation before deleting the user's primary key. */
      if (yes && pkt->pkttype != PKT_PUBLIC_SUBKEY)
        yes = cpr_get_answer_is_yes ("delete_key.secret.primary.okay",
                                     _("This is the primary key! - really delete? (y/N) "));
    }

  return yes;
}

/****************
 * Delete a public or secret key from a keyring.
 * r_sec_avail will be set if a secret key is available and the public
 * key can't be deleted for that reason.
 */
static gpg_error_t
do_delete_key (ctrl_t ctrl, const char *username, int secret, int force,
               int *r_sec_avail)
{
  gpg_error_t err;
  kbnode_t keyblock = NULL;
  kbnode_t node, kbctx;
  kbnode_t targetnode;
  KEYDB_HANDLE hd;
  PKT_public_key *pk = NULL;
  u32 keyid[2];
  int okay=0;
  KEYDB_SEARCH_DESC desc;
  int exactmatch;  /* True if key was found by fingerprint.  */
  int thiskeyonly; /* 0 = false, 1 = is primary key, 2 = is a subkey.  */

  *r_sec_avail = 0;

  hd = keydb_new ();
  if (!hd)
    return gpg_error_from_syserror ();

  /* Search the userid.  */
  err = classify_user_id (username, &desc, 1);
  exactmatch = (desc.mode == KEYDB_SEARCH_MODE_FPR);
  thiskeyonly = desc.exact;
  if (!err)
    err = keydb_search (hd, &desc, 1, NULL);
  if (err)
    {
      log_error (_("key \"%s\" not found: %s\n"), username, gpg_strerror (err));
      write_status_text (STATUS_DELETE_PROBLEM, "1");
      goto leave;
    }

  /* Read the keyblock.  */
  err = keydb_get_keyblock (hd, &keyblock);
  if (err)
    {
      log_error (_("error reading keyblock: %s\n"), gpg_strerror (err) );
      goto leave;
    }

  /* Get the keyid from the keyblock.  */
  node = find_kbnode( keyblock, PKT_PUBLIC_KEY );
  if (!node)
    {
      log_error ("Oops; key not found anymore!\n");
      err = gpg_error (GPG_ERR_GENERAL);
      goto leave;
    }

  /* If an operation only on a subkey is requested, find that subkey
   * now.  */
  if (thiskeyonly)
    {
      kbnode_t tmpnode;

      for (kbctx=NULL; (tmpnode = walk_kbnode (keyblock, &kbctx, 0)); )
        {
          if (!(tmpnode->pkt->pkttype == PKT_PUBLIC_KEY
                || tmpnode->pkt->pkttype == PKT_PUBLIC_SUBKEY))
            continue;
          if (exact_subkey_match_p (&desc, tmpnode))
            break;
        }
      if (!tmpnode)
        {
          log_error ("Oops; requested subkey not found anymore!\n");
          err = gpg_error (GPG_ERR_GENERAL);
          goto leave;
        }
      /* Set NODE to this specific subkey or primary key.  */
      thiskeyonly = node == tmpnode? 1 : 2;
      targetnode = tmpnode;
    }
  else
    targetnode = node;

  pk = targetnode->pkt->pkt.public_key;
  keyid_from_pk (pk, keyid);

  if (!secret && !force)
    {
      if (have_secret_key_with_kid (keyid))
        {
          *r_sec_avail = 1;
          err = gpg_error (GPG_ERR_EOF);
          goto leave;
        }
      else
        err = 0;
    }

  if (secret && !have_secret_key_with_kid (keyid))
    {
      err = gpg_error (GPG_ERR_NOT_FOUND);
      log_error (_("key \"%s\" not found\n"), username);
      write_status_text (STATUS_DELETE_PROBLEM, "1");
      goto leave;
    }


  if (opt.batch && exactmatch)
    okay++;
  else if (opt.batch && secret)
    {
      log_error(_("can't do this in batch mode\n"));
      log_info (_("(unless you specify the key by fingerprint)\n"));
    }
  else if (opt.batch && opt.answer_yes)
    okay++;
  else if (opt.batch)
    {
      log_error(_("can't do this in batch mode without \"--yes\"\n"));
      log_info (_("(unless you specify the key by fingerprint)\n"));
    }
  else
    okay++;

  if (okay)
    {

      if (thiskeyonly == 1 && !secret)
        {
          /* We need to delete the entire public key despite the use
           * of the thiskeyonly request.  */
          tty_printf (_("Note: The public primary key and all its subkeys"
                        " will be deleted.\n"));
        }
      else if (thiskeyonly == 2 && !secret)
        {
          tty_printf (_("Note: Only the shown public subkey"
                        " will be deleted.\n"));
        }
      if (thiskeyonly == 1 && secret)
        {
          tty_printf (_("Note: Only the secret part of the shown primary"
                        " key will be deleted.\n"));
        }
      else if (thiskeyonly == 2 && secret)
        {
          tty_printf (_("Note: Only the secret part of the shown subkey"
                        " will be deleted.\n"));
        }


      if (secret)
	{
          gpg_error_t firsterr = 0;

          setup_main_keyids (keyblock);
          for (kbctx=NULL; (node = walk_kbnode (keyblock, &kbctx, 0)); )
            {
              if (!(node->pkt->pkttype == PKT_PUBLIC_KEY
                    || node->pkt->pkttype == PKT_PUBLIC_SUBKEY))
                continue;

              if (thiskeyonly && targetnode != node)
                continue;

              if (confirm_deletion (ctrl, node->pkt, secret, exactmatch))
                {
                  err = agent_delete_secret_key (ctrl,
                                                 node->pkt->pkt.public_key);

                  if (err == GPG_ERR_NO_SECKEY)
                    continue; /* No secret key for that public (sub)key.  */

                  else if (err)
                    {
                      if (gpg_err_code (err) == GPG_ERR_KEY_ON_CARD)
                        write_status_text (STATUS_DELETE_PROBLEM, "1");

                      log_error (_("deleting secret %s failed: %s\n"),
                                 (node->pkt->pkttype == PKT_PUBLIC_KEY
                                  ? _("key") : _("subkey")),
                                 gpg_strerror (err));

                      if (!firsterr)
                        firsterr = err;

                      if (gpg_err_code (err) == GPG_ERR_CANCELED
                          || gpg_err_code (err) == GPG_ERR_FULLY_CANCELED)
		                    {
		                      write_status_error ("delete_key.secret", err);
		                      break;
		                    }
                    }
                }
            }

          err = firsterr;
          if (firsterr)
            goto leave;
	}
      else if (thiskeyonly == 2)
        {
          int selected = 0;

          /* Delete the specified public subkey.  */
          for (kbctx=NULL; (node = walk_kbnode (keyblock, &kbctx, 0)); )
            {
              if (thiskeyonly && targetnode != node)
                continue;

              if (node->pkt->pkttype == PKT_PUBLIC_SUBKEY)
                {
                  selected = targetnode == node;
                  if (selected)
                    {
                      if (confirm_deletion (ctrl, node->pkt, secret, exactmatch))
                        delete_kbnode (node);
                      else
                        selected = 0; /* Canceled: don't delete signatures. */
                    }
                }
              else if (selected && node->pkt->pkttype == PKT_SIGNATURE)
                delete_kbnode (node);
              else
                selected = 0;
            }
          commit_kbnode (&keyblock);
          err = keydb_update_keyblock (ctrl, hd, keyblock);
          if (err)
            {
              log_error (_("update failed: %s\n"), gpg_strerror (err));
              goto leave;
            }
        }
      else
	{
    if (confirm_deletion (ctrl, targetnode->pkt, secret, exactmatch))
      {
        err = keydb_delete_keyblock (hd);
        if (err)
          {
            log_error (_("deleting keyblock failed: %s\n"),
                       gpg_strerror (err));
            goto leave;
          }
      }
	}

      /* Note that the ownertrust being cleared will trigger a
	 revalidation_mark().  This makes sense - only deleting keys
	 that have ownertrust set should trigger this. */

      if (!secret && pk && !opt.dry_run && thiskeyonly != 2
          && clear_ownertrusts (ctrl, pk))
        {
          if (opt.verbose)
            log_info (_("ownertrust information cleared\n"));
        }
    }

 leave:
  keydb_release (hd);
  release_kbnode (keyblock);
  return err;
}


/*
 * Delete a public or secret key from a keyring.
 */
gpg_error_t
delete_keys (ctrl_t ctrl, strlist_t names, int secret, int allow_both)
{
  gpg_error_t err;
  int avail;
  int force = (!allow_both && !secret && opt.expert);

  /* Force allows us to delete a public key even if a secret key
     exists. */

  for ( ;names ; names=names->next )
    {
      err = do_delete_key (ctrl, names->d, secret, force, &avail);
      if (err && avail)
        {
          if (allow_both)
            {
              err = do_delete_key (ctrl, names->d, 1, 0, &avail);
              if (!err)
                err = do_delete_key (ctrl, names->d, 0, 0, &avail);
            }
          else
            {
              log_error (_("there is a secret key for public key \"%s\"!\n"),
                         names->d);
              log_info(_("use option \"--delete-secret-keys\" to delete"
                         " it first.\n"));
              write_status_text (STATUS_DELETE_PROBLEM, "2");
              return err;
            }
        }

      if (err)
        {
          log_error ("%s: delete key failed: %s\n",
                     names->d, gpg_strerror (err));
          return err;
        }
    }

  return 0;
}
