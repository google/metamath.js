include "cin.mm"
include "cun.mm"
include "cv.mm"
include "wcel.mm"
include "wo.mm"
include "wa.mm"
include "elin.mm"
include "orbi2i.mm"
include "ordi.mm"
include "elun.mm"
include "anbi12i.mm"
include "bitr2i.mm"
include "3bitri.mm"
include "uneqri.mm"

theorem undi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A u. ( B i^i C ) ) = ( ( A u. B ) i^i ( A u. C ) )

  proof
    vx
    cA
    cB
    cC
    cin
    #
    cA
    cB
    cun
    #
    cA
    cC
    cun
    #
    cin
    #
    vx
    cv
    #
    cA
    wcel
    #
    @4
    @0
    wcel
    #
    wo
    @5
    @4
    cB
    wcel
    #
    @4
    cC
    wcel
    #
    wa
    #
    wo
    @5
    @7
    wo
    #
    @5
    @8
    wo
    #
    wa
    #
    @4
    @3
    wcel
    #
    @6
    @9
    @5
    @4
    cB
    cC
    elin
    orbi2i
    @5
    @7
    @8
    ordi
    @13
    @4
    @1
    wcel
    #
    @4
    @2
    wcel
    #
    wa
    @12
    @4
    @1
    @2
    elin
    @14
    @10
    @15
    @11
    @4
    cA
    cB
    elun
    @4
    cA
    cC
    elun
    anbi12i
    bitr2i
    3bitri
    uneqri
end
