include "wcel.mm"
include "cmgm.mm"
include "cv.mm"
include "cop.mm"
include "csn.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "csgrp.mm"
include "mgm1.mm"
include "cfv.mm"
include "df-ov.mm"
include "cvv.mm"
include "opex.mm"
include "fvsng.mm"
include "mpan.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "ralsng.mm"
include "oveq2.mm"
include "ralbidv.mm"
include "3bitrd.mm"
include "mpbird.mm"
include "cbs.mm"
include "snex.mm"
include "grpbase.mm"
include "ax-mp.mm"
include "cplusg.mm"
include "grpplusg.mm"
include "issgrp.mm"
include "sylanbrc.mm"

theorem sgrp1
  let cI: class I
  let cM: class M
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sgrp1.m: |- M = { <. ( Base ` ndx ) , { I } >. , <. ( +g ` ndx ) , { <. <. I , I >. , I >. } >. }


  assert |- ( I e. V -> M e. SGrp )

  proof
    cI
    cV
    wcel
    #
    cM
    cmgm
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
    vz
    cv
    #
    @5
    co
    #
    @1
    @2
    @7
    @5
    co
    #
    @5
    co
    #
    wceq
    #
    vz
    cI
    csn
    #
    wral
    vy
    @12
    wral
    #
    vx
    @12
    wral
    #
    cM
    csgrp
    wcel
    cI
    cM
    cV
    sgrp1.m
    mgm1
    @0
    @14
    cI
    cI
    @5
    co
    #
    cI
    @5
    co
    #
    cI
    @15
    @5
    co
    #
    wceq
    #
    @0
    @16
    @15
    @17
    @0
    @15
    cI
    cI
    @5
    @0
    @15
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
    @19
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
    oveq1d
    @0
    @15
    cI
    cI
    @5
    @20
    oveq2d
    eqtr4d
    @0
    @14
    cI
    @2
    @5
    co
    #
    @7
    @5
    co
    #
    cI
    @9
    @5
    co
    #
    wceq
    #
    vz
    @12
    wral
    #
    vy
    @12
    wral
    #
    @15
    @7
    @5
    co
    #
    cI
    cI
    @7
    @5
    co
    #
    @5
    co
    #
    wceq
    #
    vz
    @12
    wral
    #
    @18
    @13
    @26
    vx
    cI
    cV
    @1
    cI
    wceq
    #
    @11
    @24
    vy
    vz
    @12
    @12
    @32
    @8
    @22
    @10
    @23
    @32
    @6
    @21
    @7
    @5
    @1
    cI
    @2
    @5
    oveq1
    oveq1d
    @1
    cI
    @9
    @5
    oveq1
    eqeq12d
    2ralbidv
    ralsng
    @25
    @31
    vy
    cI
    cV
    @2
    cI
    wceq
    #
    @24
    @30
    vz
    @12
    @33
    @22
    @27
    @23
    @29
    @33
    @21
    @15
    @7
    @5
    @2
    cI
    cI
    @5
    oveq2
    oveq1d
    @33
    @9
    @28
    cI
    @5
    @2
    cI
    @7
    @5
    oveq1
    oveq2d
    eqeq12d
    ralbidv
    ralsng
    @30
    @18
    vz
    cI
    cV
    @7
    cI
    wceq
    #
    @27
    @16
    @29
    @17
    @7
    cI
    @15
    @5
    oveq2
    @34
    @28
    @15
    cI
    @5
    @7
    cI
    cI
    @5
    oveq2
    oveq2d
    eqeq12d
    ralsng
    3bitrd
    mpbird
    vx
    vy
    vz
    @12
    cM
    @5
    @12
    cvv
    wcel
    @12
    cM
    cbs
    cfv
    wceq
    cI
    snex
    @12
    @5
    cM
    cvv
    sgrp1.m
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
    @12
    @5
    cM
    cvv
    sgrp1.m
    grpplusg
    ax-mp
    issgrp
    sylanbrc
end
