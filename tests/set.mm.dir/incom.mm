include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "ancom.mm"
include "elin.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem incom
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A i^i B ) = ( B i^i A )

  proof
    vx
    cA
    cB
    cin
    #
    cB
    cA
    cin
    #
    vx
    cv
    #
    cA
    wcel
    #
    @2
    cB
    wcel
    #
    wa
    @4
    @3
    wa
    @2
    @0
    wcel
    @2
    @1
    wcel
    @3
    @4
    ancom
    @2
    cA
    cB
    elin
    @2
    cB
    cA
    elin
    3bitr4i
    eqriv
end
