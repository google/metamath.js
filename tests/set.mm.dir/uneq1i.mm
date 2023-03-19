include "wceq.mm"
include "cun.mm"
include "uneq1.mm"
include "ax-mp.mm"

theorem uneq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume uneq1i.1: |- A = B


  assert |- ( A u. C ) = ( B u. C )

  proof
    cA
    cB
    wceq
    cA
    cC
    cun
    cB
    cC
    cun
    wceq
    uneq1i.1
    cA
    cB
    cC
    uneq1
    ax-mp
end
