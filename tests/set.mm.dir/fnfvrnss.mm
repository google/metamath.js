include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "wf.mm"
include "crn.mm"
include "wss.mm"
include "ffnfv.mm"
include "frn.mm"
include "sylbir.mm"

theorem fnfvrnss
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint A x
  disjoint B x
  disjoint F x
  assert |- ( ( F Fn A /\ A. x e. A ( F ` x ) e. B ) -> ran F C_ B )

  proof
    cF
    cA
    wfn
    vx
    cv
    cF
    cfv
    cB
    wcel
    vx
    cA
    wral
    wa
    cA
    cB
    cF
    wf
    cF
    crn
    cB
    wss
    vx
    cA
    cB
    cF
    ffnfv
    cA
    cB
    cF
    frn
    sylbir
end
