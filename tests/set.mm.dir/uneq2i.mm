include "wceq.mm"
include "cun.mm"
include "uneq2.mm"
include "ax-mp.mm"

theorem uneq2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume uneq1i.1: |- A = B


  assert |- ( C u. A ) = ( C u. B )

  proof
    cA
    cB
    wceq
    cC
    cA
    cun
    cC
    cB
    cun
    wceq
    uneq1i.1
    cA
    cB
    cC
    uneq2
    ax-mp
end
