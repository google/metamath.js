include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "ccom.mm"
include "cv.mm"
include "cop.mm"
include "wex.mm"
include "cfv.mm"
include "wb.mm"
include "eldm2g.mm"
include "cvv.mm"
include "vex.mm"
include "opelco2g.mm"
include "mpan2.mm"
include "exbidv.mm"
include "bitrd.mm"
include "adantl.mm"
include "fvex.mm"
include "eldm2.mm"
include "wceq.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "ceqsexv.mm"
include "eqcom.mm"
include "funopfvb.mm"
include "syl5bb.mm"
include "anbi1d.mm"
include "syl5bbr.mm"
include "bitr4d.mm"

theorem dmfco
  let cA: class A
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let cX: class X


  assert |- ( ( Fun G /\ A e. dom G ) -> ( A e. dom ( F o. G ) <-> ( G ` A ) e. dom F ) )

  proof
    cG
    wfun
    #
    cA
    cG
    cdm
    #
    wcel
    #
    wa
    #
    cA
    cF
    cG
    ccom
    #
    cdm
    wcel
    #
    cA
    vx
    cv
    #
    cop
    cG
    wcel
    #
    @6
    vy
    cv
    #
    cop
    #
    cF
    wcel
    #
    wa
    #
    vx
    wex
    #
    vy
    wex
    #
    cA
    cG
    cfv
    #
    cF
    cdm
    wcel
    #
    @2
    @5
    @13
    wb
    @0
    @2
    @5
    cA
    @8
    cop
    @4
    wcel
    #
    vy
    wex
    @13
    vy
    cA
    @4
    @1
    eldm2g
    @2
    @16
    @12
    vy
    @2
    @8
    cvv
    wcel
    @16
    @12
    wb
    vy
    vex
    vx
    cA
    @8
    cF
    cG
    @1
    cvv
    opelco2g
    mpan2
    exbidv
    bitrd
    adantl
    @15
    @14
    @8
    cop
    #
    cF
    wcel
    #
    vy
    wex
    @3
    @13
    vy
    @14
    cF
    cA
    cG
    fvex
    #
    eldm2
    @3
    @18
    @12
    vy
    @18
    @6
    @14
    wceq
    #
    @10
    wa
    #
    vx
    wex
    @3
    @12
    @10
    @18
    vx
    @14
    @19
    @20
    @9
    @17
    cF
    @6
    @14
    @8
    opeq1
    eleq1d
    ceqsexv
    @3
    @21
    @11
    vx
    @3
    @20
    @7
    @10
    @20
    @14
    @6
    wceq
    @3
    @7
    @6
    @14
    eqcom
    cA
    @6
    cG
    funopfvb
    syl5bb
    anbi1d
    exbidv
    syl5bbr
    exbidv
    syl5bb
    bitr4d
end
