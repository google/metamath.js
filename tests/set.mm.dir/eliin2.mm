include "nfcv.mm"
include "eliin2f.mm"

theorem eliin2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint B x
  assert |- ( B =/= (/) -> ( A e. |^|_ x e. B C <-> A. x e. B A e. C ) )

  proof
    vx
    cA
    cB
    cC
    vx
    cB
    nfcv
    eliin2f
end
