include "cc.mm"
include "caddc.mm"
include "axaddf.mm"
include "fovcl.mm"

theorem axaddcl
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A + B ) e. CC )

  proof
    cA
    cB
    cc
    cc
    cc
    caddc
    axaddf
    fovcl
end
