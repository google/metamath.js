include "nfcv.mm"
include "cbviin.mm"

theorem cbviinv
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
  assert |- |^|_ x e. A B = |^|_ y e. A C

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
    cbviin
end
