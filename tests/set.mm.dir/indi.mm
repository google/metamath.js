include "cun.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wo.mm"
include "wa.mm"
include "andi.mm"
include "elin.mm"
include "orbi12i.mm"
include "bitr4i.mm"
include "elun.mm"
include "anbi2i.mm"
include "3bitr4i.mm"
include "ineqri.mm"

theorem indi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A i^i ( B u. C ) ) = ( ( A i^i B ) u. ( A i^i C ) )

  proof
    vx
    cA
    cB
    cC
    cun
    #
    cA
    cB
    cin
    #
    cA
    cC
    cin
    #
    cun
    #
    vx
    cv
    #
    cA
    wcel
    #
    @4
    cB
    wcel
    #
    @4
    cC
    wcel
    #
    wo
    #
    wa
    #
    @4
    @1
    wcel
    #
    @4
    @2
    wcel
    #
    wo
    #
    @5
    @4
    @0
    wcel
    #
    wa
    @4
    @3
    wcel
    @9
    @5
    @6
    wa
    #
    @5
    @7
    wa
    #
    wo
    @12
    @5
    @6
    @7
    andi
    @10
    @14
    @11
    @15
    @4
    cA
    cB
    elin
    @4
    cA
    cC
    elin
    orbi12i
    bitr4i
    @13
    @8
    @5
    @4
    cB
    cC
    elun
    anbi2i
    @4
    @1
    @2
    elun
    3bitr4i
    ineqri
end
