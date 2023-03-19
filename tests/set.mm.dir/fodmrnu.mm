include "wfo.mm"
include "wa.mm"
include "wceq.mm"
include "wfn.mm"
include "fofn.mm"
include "fndmu.mm"
include "syl2an.mm"
include "crn.mm"
include "forn.mm"
include "sylan9req.mm"
include "jca.mm"

theorem fodmrnu
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( ( F : A -onto-> B /\ F : C -onto-> D ) -> ( A = C /\ B = D ) )

  proof
    cA
    cB
    cF
    wfo
    #
    cC
    cD
    cF
    wfo
    #
    wa
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    @0
    cF
    cA
    wfn
    cF
    cC
    wfn
    @2
    @1
    cA
    cB
    cF
    fofn
    cC
    cD
    cF
    fofn
    cA
    cC
    cF
    fndmu
    syl2an
    @0
    @1
    cB
    cF
    crn
    cD
    cA
    cB
    cF
    forn
    cC
    cD
    cF
    forn
    sylan9req
    jca
end
