include "wcel.mm"
include "wral.mm"
include "wf.mm"
include "crn.mm"
include "wss.mm"
include "fmptf.mm"
include "frn.mm"
include "sylbi.mm"

theorem rnmptssf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume rnmptssf.1: |- F/_ x C
  assume rnmptssf.2: |- F = ( x e. A |-> B )

  disjoint A x
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
    rnmptssf.1
    rnmptssf.2
    fmptf
    cA
    cC
    cF
    frn
    sylbi
end
