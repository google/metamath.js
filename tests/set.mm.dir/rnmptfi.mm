include "cfn.mm"
include "wcel.mm"
include "crn.mm"
include "cmpt.mm"
include "mptfi.mm"
include "syl5eqel.mm"
include "rnfi.mm"
include "syl.mm"

theorem rnmptfi
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume rnmptfi.a: |- A = ( x e. B |-> C )

  disjoint B x
  assert |- ( B e. Fin -> ran A e. Fin )

  proof
    cB
    cfn
    wcel
    #
    cA
    cfn
    wcel
    cA
    crn
    cfn
    wcel
    @0
    cA
    vx
    cB
    cC
    cmpt
    cfn
    rnmptfi.a
    vx
    cB
    cC
    mptfi
    syl5eqel
    cA
    rnfi
    syl
end
