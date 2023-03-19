include "wcel.mm"
include "csgrp.mm"
include "cv.mm"
include "cop.mm"
include "csn.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "cmnd.mm"
include "sgrp1.mm"
include "cfv.mm"
include "df-ov.mm"
include "cvv.mm"
include "opex.mm"
include "fvsng.mm"
include "mpan.mm"
include "syl5eq.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "oveq1.mm"
include "anbi12d.mm"
include "ralsng.mm"
include "mpbir2and.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "rexsng.mm"
include "mpbird.mm"
include "cbs.mm"
include "snex.mm"
include "grpbase.mm"
include "ax-mp.mm"
include "cplusg.mm"
include "grpplusg.mm"
include "ismnddef.mm"
include "sylanbrc.mm"

theorem mnd1
  let cI: class I
  let cM: class M
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume mnd1.m: |- M = { <. ( Base ` ndx ) , { I } >. , <. ( +g ` ndx ) , { <. <. I , I >. , I >. } >. }


  assert |- ( I e. V -> M e. Mnd )

  proof
    cI
    cV
    wcel
    #
    cM
    csgrp
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cI
    cI
    cop
    #
    cI
    cop
    #
    csn
    #
    co
    #
    @2
    wceq
    #
    @2
    @1
    @5
    co
    #
    @2
    wceq
    #
    wa
    #
    vy
    cI
    csn
    #
    wral
    #
    vx
    @11
    wrex
    #
    cM
    cmnd
    wcel
    cI
    cM
    cV
    mnd1.m
    sgrp1
    @0
    @13
    cI
    @2
    @5
    co
    #
    @2
    wceq
    #
    @2
    cI
    @5
    co
    #
    @2
    wceq
    #
    wa
    #
    vy
    @11
    wral
    #
    @0
    @19
    cI
    cI
    @5
    co
    #
    cI
    wceq
    #
    @21
    @0
    @20
    @3
    @5
    cfv
    #
    cI
    cI
    cI
    @5
    df-ov
    @3
    cvv
    wcel
    @0
    @22
    cI
    wceq
    cI
    cI
    opex
    @3
    cI
    cvv
    cV
    fvsng
    mpan
    syl5eq
    #
    @23
    @18
    @21
    @21
    wa
    vy
    cI
    cV
    @2
    cI
    wceq
    #
    @15
    @21
    @17
    @21
    @24
    @14
    @20
    @2
    cI
    @2
    cI
    cI
    @5
    oveq2
    @24
    id
    #
    eqeq12d
    @24
    @16
    @20
    @2
    cI
    @2
    cI
    cI
    @5
    oveq1
    @25
    eqeq12d
    anbi12d
    ralsng
    mpbir2and
    @12
    @19
    vx
    cI
    cV
    @1
    cI
    wceq
    #
    @10
    @18
    vy
    @11
    @26
    @7
    @15
    @9
    @17
    @26
    @6
    @14
    @2
    @1
    cI
    @2
    @5
    oveq1
    eqeq1d
    @26
    @8
    @16
    @2
    @1
    cI
    @2
    @5
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    rexsng
    mpbird
    @11
    @5
    vx
    cM
    vy
    @11
    cvv
    wcel
    @11
    cM
    cbs
    cfv
    wceq
    cI
    snex
    @11
    @5
    cM
    cvv
    mnd1.m
    grpbase
    ax-mp
    @5
    cvv
    wcel
    @5
    cM
    cplusg
    cfv
    wceq
    @4
    snex
    @11
    @5
    cM
    cvv
    mnd1.m
    grpplusg
    ax-mp
    ismnddef
    sylanbrc
end
