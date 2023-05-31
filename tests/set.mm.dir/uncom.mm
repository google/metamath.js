include "cun.mm"
include "cv.mm"
include "wcel.mm"
include "wo.mm"
include "orcom.mm"
include "elun.mm"
include "bitr4i.mm"
include "uneqri.mm"

theorem uncom
  param cA: class A
  param cB: class B
  let vx: setvar x


  assert |- ( A u. B ) = ( B u. A )

  proof
    vx
    cA
    cB
    cB
    cA
    cun
    #
    vx
    cv
    #
    cA
    wcel
    #
    @1
    cB
    wcel
    #
    wo
    @3
    @2
    wo
    @1
    @0
    wcel
    @2
    @3
    orcom
    @1
    cB
    cA
    elun
    bitr4i
    uneqri
end
