include "nfcv.mm"
include "prodeq1f.mm"

theorem prodeq1
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k

  disjoint A k
  disjoint B k
  assert |- ( A = B -> prod_ k e. A C = prod_ k e. B C )

  proof
    cA
    cB
    cC
    vk
    vk
    cA
    nfcv
    vk
    cB
    nfcv
    prodeq1f
end
