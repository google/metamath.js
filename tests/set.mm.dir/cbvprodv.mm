include "nfcv.mm"
include "cbvprod.mm"

theorem cbvprodv
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  assume cbvprod.1: |- ( j = k -> B = C )

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
  disjoint f y
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A f
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint A y
  disjoint B f
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint C f
  disjoint C m
  disjoint C n
  disjoint C x
  disjoint C y
  assert |- prod_ j e. A B = prod_ k e. A C

  proof
    cA
    cB
    cC
    vj
    vk
    cbvprod.1
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
    cbvprod
end
