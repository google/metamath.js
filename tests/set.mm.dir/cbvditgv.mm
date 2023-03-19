include "nfcv.mm"
include "cbvditg.mm"

theorem cbvditgv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume cbvditg.1: |- ( x = y -> C = D )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint D x
  assert |- S_ [ A -> B ] C _d x = S_ [ A -> B ] D _d y

  proof
    vx
    vy
    cA
    cB
    cC
    cD
    cbvditg.1
    vy
    cC
    nfcv
    vx
    cD
    nfcv
    cbvditg
end
