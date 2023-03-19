include "wcel.mm"
include "c0g.mm"
include "cfv.mm"
include "csn.mm"
include "cop.mm"
include "cvv.mm"
include "cbs.mm"
include "wceq.mm"
include "snex.mm"
include "grpbase.mm"
include "ax-mp.mm"
include "eqid.mm"
include "cplusg.mm"
include "grpplusg.mm"
include "snidg.mm"
include "cv.mm"
include "co.mm"
include "velsn.mm"
include "df-ov.mm"
include "opex.mm"
include "fvsng.mm"
include "mpan.mm"
include "syl5eq.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "syl5bi.mm"
include "imp.mm"
include "oveq1.mm"
include "ismgmid2.mm"
include "eqcomd.mm"

theorem mnd1id
  let cI: class I
  let cM: class M
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  assume mnd1.m: |- M = { <. ( Base ` ndx ) , { I } >. , <. ( +g ` ndx ) , { <. <. I , I >. , I >. } >. }


  assert |- ( I e. V -> ( 0g ` M ) = I )

  proof
    cI
    cV
    wcel
    #
    cI
    cM
    c0g
    cfv
    #
    @0
    va
    cI
    csn
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
    cI
    cM
    @1
    @2
    cvv
    wcel
    @2
    cM
    cbs
    cfv
    wceq
    cI
    snex
    @2
    @5
    cM
    cvv
    mnd1.m
    grpbase
    ax-mp
    @1
    eqid
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
    @2
    @5
    cM
    cvv
    mnd1.m
    grpplusg
    ax-mp
    cI
    cV
    snidg
    @0
    va
    cv
    #
    @2
    wcel
    #
    cI
    @6
    @5
    co
    #
    @6
    wceq
    #
    @7
    @6
    cI
    wceq
    #
    @0
    @9
    va
    cI
    velsn
    #
    @0
    @9
    @10
    cI
    cI
    @5
    co
    #
    cI
    wceq
    #
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
    #
    @10
    @8
    @12
    @6
    cI
    @6
    cI
    cI
    @5
    oveq2
    @10
    id
    #
    eqeq12d
    syl5ibrcom
    syl5bi
    imp
    @0
    @7
    @6
    cI
    @5
    co
    #
    @6
    wceq
    #
    @7
    @10
    @0
    @18
    @11
    @0
    @18
    @10
    @13
    @15
    @10
    @17
    @12
    @6
    cI
    @6
    cI
    cI
    @5
    oveq1
    @16
    eqeq12d
    syl5ibrcom
    syl5bi
    imp
    ismgmid2
    eqcomd
end
