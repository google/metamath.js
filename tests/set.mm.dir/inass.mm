include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "anass.mm"
include "elin.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "anbi1i.mm"
include "3bitr4i.mm"
include "ineqri.mm"

theorem inass
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A i^i B ) i^i C ) = ( A i^i ( B i^i C ) )

  proof
    vx
    cA
    cB
    cin
    #
    cC
    cA
    cB
    cC
    cin
    #
    cin
    #
    vx
    cv
    #
    cA
    wcel
    #
    @3
    cB
    wcel
    #
    wa
    #
    @3
    cC
    wcel
    #
    wa
    #
    @4
    @3
    @1
    wcel
    #
    wa
    #
    @3
    @0
    wcel
    #
    @7
    wa
    @3
    @2
    wcel
    @8
    @4
    @5
    @7
    wa
    #
    wa
    @10
    @4
    @5
    @7
    anass
    @9
    @12
    @4
    @3
    cB
    cC
    elin
    anbi2i
    bitr4i
    @11
    @6
    @7
    @3
    cA
    cB
    elin
    anbi1i
    @3
    cA
    @1
    elin
    3bitr4i
    ineqri
end
