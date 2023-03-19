include "cgrp.mm"
include "wcel.mm"
include "cprime.mm"
include "wa.mm"
include "csn.mm"
include "cress.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "chash.mm"
include "cc0.mm"
include "cexp.mm"
include "wceq.mm"
include "cpgp.mm"
include "wbr.mm"
include "c1.mm"
include "cn.mm"
include "prmnn.mm"
include "adantl.mm"
include "nncnd.mm"
include "exp0d.mm"
include "cvv.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "csubg.mm"
include "0subg.mm"
include "adantr.mm"
include "eqid.mm"
include "subgbas.mm"
include "syl.mm"
include "fveq2d.mm"
include "syl5eqr.mm"
include "eqtr2d.mm"
include "cn0.mm"
include "wi.mm"
include "subggrp.mm"
include "simpr.mm"
include "0nn0.mm"
include "a1i.mm"
include "pgpfi1.mm"
include "syl3anc.mm"
include "mpd.mm"

theorem pgp0
  let cP: class P
  let cG: class G
  let c.0: class .0.
  assume pgp0.1: |- .0. = ( 0g ` G )


  assert |- ( ( G e. Grp /\ P e. Prime ) -> P pGrp ( G |`s { .0. } ) )

  proof
    cG
    cgrp
    wcel
    #
    cP
    cprime
    wcel
    #
    wa
    #
    cG
    c.0
    csn
    #
    cress
    co
    #
    cbs
    cfv
    #
    chash
    cfv
    #
    cP
    cc0
    cexp
    co
    #
    wceq
    #
    cP
    @4
    cpgp
    wbr
    #
    @2
    @7
    c1
    @6
    @2
    cP
    @2
    cP
    @1
    cP
    cn
    wcel
    @0
    cP
    prmnn
    adantl
    nncnd
    exp0d
    @2
    c1
    @3
    chash
    cfv
    #
    @6
    c.0
    cvv
    wcel
    @10
    c1
    wceq
    c.0
    cG
    c0g
    cfv
    cvv
    pgp0.1
    cG
    c0g
    fvex
    eqeltri
    c.0
    cvv
    hashsng
    ax-mp
    @2
    @3
    @5
    chash
    @2
    @3
    cG
    csubg
    cfv
    wcel
    #
    @3
    @5
    wceq
    @0
    @11
    @1
    cG
    c.0
    pgp0.1
    0subg
    adantr
    #
    @3
    cG
    @4
    @4
    eqid
    #
    subgbas
    syl
    fveq2d
    syl5eqr
    eqtr2d
    @2
    @4
    cgrp
    wcel
    #
    @1
    cc0
    cn0
    wcel
    #
    @8
    @9
    wi
    @2
    @11
    @14
    @12
    @3
    cG
    @4
    @13
    subggrp
    syl
    @0
    @1
    simpr
    @15
    @2
    0nn0
    a1i
    cP
    @4
    cc0
    @5
    @5
    eqid
    pgpfi1
    syl3anc
    mpd
end
