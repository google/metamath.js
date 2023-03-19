include "wcel.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "enrefg.mm"
include "breq2.mm"
include "syl5ibcom.mm"

theorem eqeng
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( A = B -> A ~~ B ) )

  proof
    cA
    cV
    wcel
    cA
    cA
    cen
    wbr
    cA
    cB
    wceq
    cA
    cB
    cen
    wbr
    cA
    cV
    enrefg
    cA
    cB
    cA
    cen
    breq2
    syl5ibcom
end
