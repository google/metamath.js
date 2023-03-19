include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "crn.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "cop.mm"
include "wex.mm"
include "funfvop.mm"
include "vex.mm"
include "opeq1.mm"
include "spcev.mm"
include "syl.mm"
include "fvex.mm"
include "elrn2.mm"
include "sylibr.mm"
include "vtoclg.mm"
include "anabsi7.mm"

theorem fvelrn
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( Fun F /\ A e. dom F ) -> ( F ` A ) e. ran F )

  proof
    cF
    wfun
    #
    cA
    cF
    cdm
    #
    wcel
    #
    cA
    cF
    cfv
    #
    cF
    crn
    #
    wcel
    #
    @0
    vx
    cv
    #
    @1
    wcel
    #
    wa
    #
    @6
    cF
    cfv
    #
    @4
    wcel
    #
    wi
    @0
    @2
    wa
    #
    @5
    wi
    vx
    cA
    @1
    @6
    cA
    wceq
    #
    @8
    @11
    @10
    @5
    @12
    @7
    @2
    @0
    @6
    cA
    @1
    eleq1
    anbi2d
    @12
    @9
    @3
    @4
    @6
    cA
    cF
    fveq2
    eleq1d
    imbi12d
    @8
    vy
    cv
    #
    @9
    cop
    #
    cF
    wcel
    #
    vy
    wex
    #
    @10
    @8
    @6
    @9
    cop
    #
    cF
    wcel
    #
    @16
    @6
    cF
    funfvop
    @15
    @18
    vy
    @6
    vx
    vex
    @13
    @6
    wceq
    @14
    @17
    cF
    @13
    @6
    @9
    opeq1
    eleq1d
    spcev
    syl
    vy
    @9
    cF
    @6
    cF
    fvex
    elrn2
    sylibr
    vtoclg
    anabsi7
end
