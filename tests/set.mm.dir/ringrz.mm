include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grpidcl.mm"
include "eqid.mm"
include "grplid.mm"
include "mpdan.mm"
include "syl.mm"
include "adantr.mm"
include "oveq2d.mm"
include "w3a.mm"
include "simpr.mm"
include "3jca.mm"
include "ringdi.mm"
include "syldan.mm"
include "ringcl.mm"
include "mpd3an3.mm"
include "eqcomd.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "wb.mm"
include "grprcan.mm"
include "syl13anc.mm"
include "mpbid.mm"

theorem ringrz
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let c.0: class .0.
  assume rngz.b: |- B = ( Base ` R )
  assume rngz.t: |- .x. = ( .r ` R )
  assume rngz.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Ring /\ X e. B ) -> ( X .x. .0. ) = .0. )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    c.0
    c.x
    co
    #
    @3
    cR
    cplusg
    cfv
    #
    co
    #
    c.0
    @3
    @4
    co
    #
    wceq
    #
    @3
    c.0
    wceq
    #
    @2
    cX
    c.0
    c.0
    @4
    co
    #
    c.x
    co
    #
    @3
    @5
    @6
    @2
    @9
    c.0
    cX
    c.x
    @0
    @9
    c.0
    wceq
    #
    @1
    @0
    cR
    cgrp
    wcel
    #
    @11
    cR
    ringgrp
    #
    @12
    c.0
    cB
    wcel
    #
    @11
    cB
    cR
    c.0
    rngz.b
    rngz.z
    grpidcl
    #
    cB
    @4
    cR
    c.0
    c.0
    rngz.b
    @4
    eqid
    #
    rngz.z
    grplid
    mpdan
    syl
    adantr
    oveq2d
    @0
    @1
    @1
    @14
    @14
    w3a
    @10
    @5
    wceq
    @2
    @1
    @14
    @14
    @0
    @1
    simpr
    @0
    @14
    @1
    @0
    @12
    @14
    @13
    @15
    syl
    adantr
    #
    @17
    3jca
    cB
    @4
    cR
    c.x
    cX
    c.0
    c.0
    rngz.b
    @16
    rngz.t
    ringdi
    syldan
    @2
    @12
    @3
    cB
    wcel
    #
    @3
    @6
    wceq
    @0
    @12
    @1
    @13
    adantr
    #
    @0
    @1
    @14
    @18
    @17
    cB
    cR
    c.x
    cX
    c.0
    rngz.b
    rngz.t
    ringcl
    mpd3an3
    #
    @12
    @18
    wa
    @6
    @3
    cB
    @4
    cR
    @3
    c.0
    rngz.b
    @16
    rngz.z
    grplid
    eqcomd
    syl2anc
    3eqtr3d
    @2
    @12
    @18
    @14
    @18
    @7
    @8
    wb
    @19
    @20
    @17
    @20
    cB
    @4
    cR
    @3
    c.0
    @3
    rngz.b
    @16
    grprcan
    syl13anc
    mpbid
end
