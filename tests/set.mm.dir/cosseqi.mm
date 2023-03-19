include "wceq.mm"
include "ccoss.mm"
include "cosseq.mm"
include "ax-mp.mm"

theorem cosseqi
  let cA: class A
  let cB: class B
  assume cosseqi.1: |- A = B


  assert |- ,~ A = ,~ B

  proof
    cA
    cB
    wceq
    cA
    ccoss
    cB
    ccoss
    wceq
    cosseqi.1
    cA
    cB
    cosseq
    ax-mp
end
