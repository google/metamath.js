include "wceq.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "eleq2.mm"
include "anbi1d.mm"
include "elin.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem ineq1
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A = B -> ( A i^i C ) = ( B i^i C ) )

  proof
    cA
    cB
    wceq
    #
    vx
    cA
    cC
    cin
    #
    cB
    cC
    cin
    #
    @0
    vx
    cv
    #
    cA
    wcel
    #
    @3
    cC
    wcel
    #
    wa
    @3
    cB
    wcel
    #
    @5
    wa
    @3
    @1
    wcel
    @3
    @2
    wcel
    @0
    @4
    @6
    @5
    cA
    cB
    @3
    eleq2
    anbi1d
    @3
    cA
    cC
    elin
    @3
    cB
    cC
    elin
    3bitr4g
    eqrdv
end
