include "nfcv.mm"
include "cbvixp.mm"

theorem cbvixpv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume cbvixpv.1: |- ( x = y -> B = C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C x
  assert |- X_ x e. A B = X_ y e. A C

  proof
    vx
    vy
    cA
    cB
    cC
    vy
    cB
    nfcv
    vx
    cC
    nfcv
    cbvixpv.1
    cbvixp
end
