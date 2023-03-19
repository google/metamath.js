include "nfcv.mm"
include "csbief.mm"

theorem csbie
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume csbie.1: |- A e. _V
  assume csbie.2: |- ( x = A -> B = C )

  disjoint A x
  disjoint C x
  assert |- [_ A / x ]_ B = C

  proof
    vx
    cA
    cB
    cC
    csbie.1
    vx
    cC
    nfcv
    csbie.2
    csbief
end
