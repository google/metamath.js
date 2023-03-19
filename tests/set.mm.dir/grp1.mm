include "wcel.mm"
include "cmnd.mm"
include "cv.mm"
include "cop.mm"
include "csn.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "cgrp.mm"
include "mnd1.mm"
include "df-ov.mm"
include "cvv.mm"
include "opex.mm"
include "fvsng.mm"
include "mpan.mm"
include "syl5eq.mm"
include "mnd1id.mm"
include "eqtr4d.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "ralsng.mm"
include "oveq1.mm"
include "rexsng.mm"
include "bitrd.mm"
include "mpbird.mm"
include "cbs.mm"
include "snex.mm"
include "grpbase.mm"
include "ax-mp.mm"
include "cplusg.mm"
include "grpplusg.mm"
include "eqid.mm"
include "isgrp.mm"
include "sylanbrc.mm"

theorem grp1
  let cI: class I
  let cM: class M
  let cV: class V
  let ve: setvar e
  let vi: setvar i
  assume grp1.m: |- M = { <. ( Base ` ndx ) , { I } >. , <. ( +g ` ndx ) , { <. <. I , I >. , I >. } >. }


  assert |- ( I e. V -> M e. Grp )

  proof
    cI
    cV
    wcel
    #
    cM
    cmnd
    wcel
    ve
    cv
    #
    vi
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
    cM
    c0g
    cfv
    #
    wceq
    #
    ve
    cI
    csn
    #
    wrex
    #
    vi
    @9
    wral
    #
    cM
    cgrp
    wcel
    cI
    cM
    cV
    grp1.m
    mnd1
    @0
    @11
    cI
    cI
    @5
    co
    #
    @7
    wceq
    #
    @0
    @12
    cI
    @7
    @0
    @12
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
    @14
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
    cI
    cM
    cV
    grp1.m
    mnd1id
    eqtr4d
    @0
    @11
    @1
    cI
    @5
    co
    #
    @7
    wceq
    #
    ve
    @9
    wrex
    #
    @13
    @10
    @17
    vi
    cI
    cV
    @2
    cI
    wceq
    #
    @8
    @16
    ve
    @9
    @18
    @6
    @15
    @7
    @2
    cI
    @1
    @5
    oveq2
    eqeq1d
    rexbidv
    ralsng
    @16
    @13
    ve
    cI
    cV
    @1
    cI
    wceq
    @15
    @12
    @7
    @1
    cI
    cI
    @5
    oveq1
    eqeq1d
    rexsng
    bitrd
    mpbird
    @9
    @5
    ve
    cM
    @7
    vi
    @9
    cvv
    wcel
    @9
    cM
    cbs
    cfv
    wceq
    cI
    snex
    @9
    @5
    cM
    cvv
    grp1.m
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
    @9
    @5
    cM
    cvv
    grp1.m
    grpplusg
    ax-mp
    @7
    eqid
    isgrp
    sylanbrc
end
