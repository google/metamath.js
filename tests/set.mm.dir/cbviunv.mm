include "nfcv.mm"
include "cbviun.mm"

theorem cbviunv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume cbviunv.1: |- ( x = y -> B = C )

  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  assert |- U_ x e. A B = U_ y e. A C

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
    cbviunv.1
    cbviun
end
