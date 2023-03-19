include "nfcv.mm"
include "ssiinf.mm"

theorem ssiin
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint C x
  assert |- ( C C_ |^|_ x e. A B <-> A. x e. A C C_ B )

  proof
    vx
    cA
    cB
    cC
    vx
    cC
    nfcv
    ssiinf
end
