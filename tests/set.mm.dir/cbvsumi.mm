include "nfcv.mm"
include "cbvsum.mm"

theorem cbvsumi
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  assume cbvsumi.1: |- F/_ k B
  assume cbvsumi.2: |- F/_ j C
  assume cbvsumi.3: |- ( j = k -> B = C )

  disjoint j k
  disjoint A j
  disjoint A k
  assert |- sum_ j e. A B = sum_ k e. A C

  proof
    cA
    cB
    cC
    vj
    vk
    cbvsumi.3
    vk
    cA
    nfcv
    vj
    cA
    nfcv
    cbvsumi.1
    cbvsumi.2
    cbvsum
end
