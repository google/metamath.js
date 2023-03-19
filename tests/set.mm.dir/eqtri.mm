include "wceq.mm"
include "eqeq2i.mm"
include "mpbi.mm"

theorem eqtri
  param cA: class A
  param cB: class B
  param cC: class C
  assume eqtri.1: |- A = B
  assume eqtri.2: |- B = C


  assert |- A = C

  proof
    cA
    cB
    wceq
    cA
    cC
    wceq
    eqtri.1
    cB
    cC
    cA
    eqtri.2
    eqeq2i
    mpbi
end
