include "cv.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "cvv.mm"
include "exsimpl.mm"
include "df-clel.mm"
include "isset.mm"
include "3imtr4i.mm"

theorem elex
  param cA: class A
  param cB: class B
  let vx: setvar x


  assert |- ( A e. B -> A e. _V )

  proof
    vx
    cv
    #
    cA
    wceq
    #
    @0
    cB
    wcel
    #
    wa
    vx
    wex
    @1
    vx
    wex
    cA
    cB
    wcel
    cA
    cvv
    wcel
    @1
    @2
    vx
    exsimpl
    vx
    cA
    cB
    df-clel
    vx
    cA
    isset
    3imtr4i
end
