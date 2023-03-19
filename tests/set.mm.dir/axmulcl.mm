include "cc.mm"
include "cmul.mm"
include "axmulf.mm"
include "fovcl.mm"

theorem axmulcl
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A x. B ) e. CC )

  proof
    cA
    cB
    cc
    cc
    cc
    cmul
    axmulf
    fovcl
end
