include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "dfss2.mm"
include "mpgbir.mm"

theorem ssriv
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ssriv.1: |- ( x e. A -> x e. B )

  disjoint A x
  disjoint B x
  assert |- A C_ B

  proof
    cA
    cB
    wss
    vx
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
    wi
    vx
    vx
    cA
    cB
    dfss2
    ssriv.1
    mpgbir
end
