include "nfcv.mm"
include "cbvprod.mm"

theorem cbvprodi
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  assume cbvprodi.1: |- F/_ k B
  assume cbvprodi.2: |- F/_ j C
  assume cbvprodi.3: |- ( j = k -> B = C )

  disjoint j k
  disjoint A j
  disjoint A k
  assert |- prod_ j e. A B = prod_ k e. A C

  proof
    cA
    cB
    cC
    vj
    vk
    cbvprodi.3
    vk
    cA
    nfcv
    vj
    cA
    nfcv
    cbvprodi.1
    cbvprodi.2
    cbvprod
end
