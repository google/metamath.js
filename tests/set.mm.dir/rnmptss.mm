include "wcel.mm"
include "wral.mm"
include "wf.mm"
include "crn.mm"
include "wss.mm"
include "fmpt.mm"
include "frn.mm"
include "sylbi.mm"

theorem rnmptss
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume rnmptss.1: |- F = ( x e. A |-> B )

  disjoint A x
  disjoint C x
  assert |- ( A. x e. A B e. C -> ran F C_ C )

  proof
    cB
    cC
    wcel
    vx
    cA
    wral
    cA
    cC
    cF
    wf
    cF
    crn
    cC
    wss
    vx
    cA
    cC
    cB
    cF
    rnmptss.1
    fmpt
    cA
    cC
    cF
    frn
    sylbi
end
