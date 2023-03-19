include "nfcv.mm"
include "cbvdisj.mm"

theorem cbvdisjv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume cbvdisjv.1: |- ( x = y -> B = C )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  assert |- ( Disj_ x e. A B <-> Disj_ y e. A C )

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
    cbvdisjv.1
    cbvdisj
end
