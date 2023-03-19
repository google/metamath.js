include "nfcv.mm"
include "cbvesum.mm"

theorem cbvesumv
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  assume cbvesum.1: |- ( j = k -> B = C )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint B k
  disjoint C j
  assert |- sum* j e. A B = sum* k e. A C

  proof
    cA
    cB
    cC
    vj
    vk
    cbvesum.1
    vk
    cA
    nfcv
    vj
    cA
    nfcv
    vk
    cB
    nfcv
    vj
    cC
    nfcv
    cbvesum
end
