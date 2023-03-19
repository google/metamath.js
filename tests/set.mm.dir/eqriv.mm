include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "dfcleq.mm"
include "mpgbir.mm"

theorem eqriv
  param vx: setvar x
  param cA: class A
  param cB: class B
  assume eqriv.1: |- ( x e. A <-> x e. B )

  disjoint A x
  disjoint B x
  assert |- A = B

  proof
    cA
    cB
    wceq
    vx
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
    wb
    vx
    vx
    cA
    cB
    dfcleq
    eqriv.1
    mpgbir
end
