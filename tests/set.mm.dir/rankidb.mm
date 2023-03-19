include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "cv.mm"
include "csuc.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "crnk.mm"
include "wrex.mm"
include "rankwflemb.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfint.mm"
include "nfsuc.mm"
include "nffv.mm"
include "nfel2.mm"
include "wceq.mm"
include "suceq.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "onminsb.mm"
include "sylbi.mm"
include "rankvalb.mm"
include "syl.mm"
include "eleqtrrd.mm"

theorem rankidb
  let cA: class A
  let vx: setvar x


  assert |- ( A e. U. ( R1 " On ) -> A e. ( R1 ` suc ( rank ` A ) ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    wcel
    #
    cA
    cA
    vx
    cv
    #
    csuc
    #
    cr1
    cfv
    #
    wcel
    #
    vx
    con0
    crab
    #
    cint
    #
    csuc
    #
    cr1
    cfv
    #
    cA
    crnk
    cfv
    #
    csuc
    #
    cr1
    cfv
    @0
    @4
    vx
    con0
    wrex
    cA
    @8
    wcel
    #
    vx
    cA
    rankwflemb
    @4
    @11
    vx
    vx
    cA
    @8
    vx
    @7
    cr1
    vx
    cr1
    nfcv
    vx
    @6
    vx
    @5
    @4
    vx
    con0
    nfrab1
    nfint
    nfsuc
    nffv
    nfel2
    @1
    @6
    wceq
    #
    @3
    @8
    cA
    @12
    @2
    @7
    cr1
    @1
    @6
    suceq
    fveq2d
    eleq2d
    onminsb
    sylbi
    @0
    @10
    @7
    cr1
    @0
    @9
    @6
    wceq
    @10
    @7
    wceq
    vx
    cA
    rankvalb
    @9
    @6
    suceq
    syl
    fveq2d
    eleqtrrd
end
