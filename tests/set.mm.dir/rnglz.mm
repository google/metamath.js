include "crng.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "cgrp.mm"
include "cabl.mm"
include "rngabl.mm"
include "ablgrp.mm"
include "syl.mm"
include "grpidcl.mm"
include "eqid.mm"
include "grplid.mm"
include "mpdan.mm"
include "adantr.mm"
include "oveq1d.mm"
include "w3a.mm"
include "simpl.mm"
include "jca.mm"
include "anim1i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "rngdir.mm"
include "syl2anc.mm"
include "simpr.mm"
include "rngcl.mm"
include "syl3anc.mm"
include "grprid.mm"
include "eqcomd.mm"
include "3eqtr3d.mm"
include "wb.mm"
include "grplcan.mm"
include "syl13anc.mm"
include "mpbid.mm"

theorem rnglz
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let c.0: class .0.
  let vk: setvar k
  let vx: setvar x
  assume rngcl.b: |- B = ( Base ` R )
  assume rngcl.t: |- .x. = ( .r ` R )
  assume rnglz.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Rng /\ X e. B ) -> ( .0. .x. X ) = .0. )

  proof
    cR
    crng
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    c.0
    cX
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
    @3
    c.0
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
    c.0
    c.0
    @4
    co
    #
    cX
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
    @0
    cR
    cabl
    wcel
    @12
    cR
    rngabl
    cR
    ablgrp
    syl
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
    rngcl.b
    rnglz.z
    grpidcl
    #
    cB
    @4
    cR
    c.0
    c.0
    rngcl.b
    @4
    eqid
    #
    rnglz.z
    grplid
    mpdan
    syl
    adantr
    oveq1d
    @2
    @0
    @14
    @14
    @1
    w3a
    #
    @10
    @5
    wceq
    @0
    @1
    simpl
    #
    @2
    @14
    @14
    wa
    #
    @1
    wa
    @17
    @0
    @19
    @1
    @0
    @14
    @14
    @0
    @12
    @14
    @13
    @15
    syl
    #
    @20
    jca
    anim1i
    @14
    @14
    @1
    df-3an
    sylibr
    cB
    @4
    cR
    c.x
    c.0
    c.0
    cX
    rngcl.b
    @16
    rngcl.t
    rngdir
    syl2anc
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
    @2
    @0
    @14
    @1
    @21
    @18
    @0
    @14
    @1
    @20
    adantr
    #
    @0
    @1
    simpr
    cB
    cR
    c.x
    c.0
    cX
    rngcl.b
    rngcl.t
    rngcl
    syl3anc
    #
    @12
    @21
    wa
    @6
    @3
    cB
    @4
    cR
    @3
    c.0
    rngcl.b
    @16
    rnglz.z
    grprid
    eqcomd
    syl2anc
    3eqtr3d
    @2
    @12
    @21
    @14
    @21
    @7
    @8
    wb
    @22
    @24
    @23
    @24
    cB
    @4
    cR
    @3
    c.0
    @3
    rngcl.b
    @16
    grplcan
    syl13anc
    mpbid
end
