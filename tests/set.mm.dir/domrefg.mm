include "wcel.mm"
include "cen.mm"
include "wbr.mm"
include "cdom.mm"
include "enrefg.mm"
include "endom.mm"
include "syl.mm"

theorem domrefg
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> A ~<_ A )

  proof
    cA
    cV
    wcel
    cA
    cA
    cen
    wbr
    cA
    cA
    cdom
    wbr
    cA
    cV
    enrefg
    cA
    cA
    endom
    syl
end
