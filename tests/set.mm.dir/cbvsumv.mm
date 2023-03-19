include "nfcv.mm"
include "cbvsum.mm"

theorem cbvsumv
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  assume cbvsum.1: |- ( j = k -> B = C )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint B k
  disjoint C j
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint n x
  disjoint A f
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint B f
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint C f
  disjoint C m
  disjoint C n
  disjoint C x
  assert |- sum_ j e. A B = sum_ k e. A C

  proof
    cA
    cB
    cC
    vj
    vk
    cbvsum.1
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
    cbvsum
end
