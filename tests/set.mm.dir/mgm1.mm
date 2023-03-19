include "wcel.mm"
include "cmgm.mm"
include "cv.mm"
include "cop.mm"
include "csn.mm"
include "co.mm"
include "wral.mm"
include "cfv.mm"
include "df-ov.mm"
include "cvv.mm"
include "wceq.mm"
include "opex.mm"
include "fvsng.mm"
include "mpan.mm"
include "syl5eq.mm"
include "snidg.mm"
include "eqeltrd.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "ralsng.mm"
include "oveq2.mm"
include "bitrd.mm"
include "mpbird.mm"
include "wb.mm"
include "cbs.mm"
include "snex.mm"
include "grpbase.mm"
include "ax-mp.mm"
include "cplusg.mm"
include "grpplusg.mm"
include "ismgmn0.mm"
include "syl.mm"

theorem mgm1
  let cI: class I
  let cM: class M
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume mgm1.m: |- M = { <. ( Base ` ndx ) , { I } >. , <. ( +g ` ndx ) , { <. <. I , I >. , I >. } >. }


  assert |- ( I e. V -> M e. Mgm )

  proof
    cI
    cV
    wcel
    #
    cM
    cmgm
    wcel
    #
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
    cI
    csn
    #
    wcel
    #
    vy
    @8
    wral
    #
    vx
    @8
    wral
    #
    @0
    @11
    cI
    cI
    @6
    co
    #
    @8
    wcel
    #
    @0
    @12
    cI
    @8
    @0
    @12
    @4
    @6
    cfv
    #
    cI
    cI
    cI
    @6
    df-ov
    @4
    cvv
    wcel
    @0
    @14
    cI
    wceq
    cI
    cI
    opex
    @4
    cI
    cvv
    cV
    fvsng
    mpan
    syl5eq
    cI
    cV
    snidg
    #
    eqeltrd
    @0
    @11
    cI
    @3
    @6
    co
    #
    @8
    wcel
    #
    vy
    @8
    wral
    #
    @13
    @10
    @18
    vx
    cI
    cV
    @2
    cI
    wceq
    #
    @9
    @17
    vy
    @8
    @19
    @7
    @16
    @8
    @2
    cI
    @3
    @6
    oveq1
    eleq1d
    ralbidv
    ralsng
    @17
    @13
    vy
    cI
    cV
    @3
    cI
    wceq
    @16
    @12
    @8
    @3
    cI
    cI
    @6
    oveq2
    eleq1d
    ralsng
    bitrd
    mpbird
    @0
    cI
    @8
    wcel
    @1
    @11
    wb
    @15
    vx
    vy
    cI
    @8
    cM
    @6
    @8
    cvv
    wcel
    @8
    cM
    cbs
    cfv
    wceq
    cI
    snex
    @8
    @6
    cM
    cvv
    mgm1.m
    grpbase
    ax-mp
    @6
    cvv
    wcel
    @6
    cM
    cplusg
    cfv
    wceq
    @5
    snex
    @8
    @6
    cM
    cvv
    mgm1.m
    grpplusg
    ax-mp
    ismgmn0
    syl
    mpbird
end
