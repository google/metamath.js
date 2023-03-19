include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "breq.mm"
include "ax-mp.mm"

theorem breqi
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  assume breqi.1: |- R = S


  assert |- ( A R B <-> A S B )

  proof
    cR
    cS
    wceq
    cA
    cB
    cR
    wbr
    cA
    cB
    cS
    wbr
    wb
    breqi.1
    cA
    cB
    cR
    cS
    breq
    ax-mp
end
