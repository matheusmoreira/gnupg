/* revoke.c
 *	Copyright (C) 1998 Free Software Foundation, Inc.
 *
 * This file is part of GnuPG.
 *
 * GnuPG is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * GnuPG is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */

#include <config.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <assert.h>

#include "options.h"
#include "packet.h"
#include "errors.h"
#include "keydb.h"
#include "memory.h"
#include "util.h"
#include "main.h"
#include "ttyio.h"
#include "status.h"
#include "i18n.h"


/****************
 * Generate a revocation certificate for UNAME
 */
int
gen_revoke( const char *uname )
{
    int rc = 0;
    armor_filter_context_t afx;
    compress_filter_context_t zfx;
    PACKET pkt;
    PKT_secret_key *sk; /* used as pointer into a kbnode */
    PKT_public_key *pk = NULL;
    PKT_signature *sig = NULL;
    u32 sk_keyid[2];
    IOBUF out = NULL;
    KBNODE keyblock = NULL;
    KBNODE node;
    KBPOS kbpos;

    if( opt.batch ) {
	log_error(_("sorry, can't do this in batch mode\n"));
	return G10ERR_GENERAL;
    }


    /* FIXME: ask for the reason of revocation
       0x00 - No reason specified (key revocations or cert revocations)
    Does not make sense!

       0x01 - Key is superceded (key revocations)
       0x02 - Key material has been compromised (key revocations)
       0x03 - Key is no longer used (key revocations)
       0x20 - User id information is no longer valid (cert revocations)

       Following the revocation code is a string of octets which gives
      information about the reason for revocation in human-readable form
     */

    memset( &afx, 0, sizeof afx);
    memset( &zfx, 0, sizeof zfx);
    init_packet( &pkt );


    /* search the userid */
    rc = find_secret_keyblock_byname( &kbpos, uname );
    if( rc ) {
	log_error(_("secret key for user `%s' not found\n"), uname );
	goto leave;
    }

    /* read the keyblock */
    rc = read_keyblock( &kbpos, &keyblock );
    if( rc ) {
	log_error(_("error reading the certificate: %s\n"), g10_errstr(rc) );
	goto leave;
    }

    /* get the keyid from the keyblock */
    node = find_kbnode( keyblock, PKT_SECRET_KEY );
    if( !node ) { /* maybe better to use log_bug ? */
	log_error(_("Oops; secret key not found anymore!\n"));
	rc = G10ERR_GENERAL;
	goto leave;
    }

    /* fixme: should make a function out of this stuff,
     * it's used all over the source */
    sk = node->pkt->pkt.secret_key;
    keyid_from_sk( sk, sk_keyid );
    tty_printf("\nsec  %4u%c/%08lX %s   ",
	      nbits_from_sk( sk ),
	      pubkey_letter( sk->pubkey_algo ),
	      sk_keyid[1], datestr_from_sk(sk) );
    {
	size_t n;
	char *p = get_user_id( sk_keyid, &n );
	tty_print_string( p, n );
	m_free(p);
	tty_printf("\n");
    }
    pk = m_alloc_clear( sizeof *pk );
    rc = get_pubkey( pk, sk_keyid );
    if( rc ) {
	log_error(_("no corresponding public key: %s\n"), g10_errstr(rc) );
	goto leave;
    }
    if( cmp_public_secret_key( pk, sk ) ) {
	log_error(_("public key does not match secret key!\n") );
	rc = G10ERR_GENERAL;
	goto leave;
    }

    tty_printf("\n");
    if( !cpr_get_answer_is_yes("gen_revoke.okay",
			_("Create a revocation certificate for this key? ")) ){
	rc = 0;
	goto leave;
    }

    switch( is_secret_key_protected( sk ) ) {
      case -1:
	log_error(_("unknown protection algorithm\n"));
	rc = G10ERR_PUBKEY_ALGO;
	break;
      case 0:
	tty_printf(_("NOTE: This key is not protected!\n"));
	break;
      default:
	rc = check_secret_key( sk, 0 );
	break;
    }
    if( rc )
	goto leave;


    if( !opt.armor )
	tty_printf(_("ASCII armored output forced.\n"));

    if( (rc = open_outfile( NULL, 0, &out )) )
	goto leave;

    afx.what = 1;
    afx.hdrlines = "Comment: A revocation certificate should follow\n";
    iobuf_push_filter( out, armor_filter, &afx );

    /* create it */
    rc = make_keysig_packet( &sig, pk, NULL, NULL, sk, 0x20, 0, NULL, NULL);
    if( rc ) {
	log_error(_("make_keysig_packet failed: %s\n"), g10_errstr(rc));
	goto leave;
    }
    init_packet( &pkt );
    pkt.pkttype = PKT_SIGNATURE;
    pkt.pkt.signature = sig;

    rc = build_packet( out, &pkt );
    if( rc ) {
	log_error(_("build_packet failed: %s\n"), g10_errstr(rc) );
	goto leave;
    }

    /* and issue a usage notice */
    tty_printf(_("Revocation certificate created.\n\n"
"Please move it to a medium which you can hide away; if Mallory gets\n"
"access to this certificate he can use it to make your key unusable.\n"
"It is smart to print this certificate and store it away, just in case\n"
"your media become unreadable.  But have some caution:  The print system of\n"
"your machine might store the data and make it available to others!\n"));



  leave:
    if( pk )
	free_public_key( pk );
    if( sig )
	free_seckey_enc( sig );
    release_kbnode( keyblock );
    if( rc )
	iobuf_cancel(out);
    else
	iobuf_close(out);
    return rc;
}


