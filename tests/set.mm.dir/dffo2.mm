include "wfo.mm"
include "wf.mm"
include "crn.mm"
include "wceq.mm"
include "wa.mm"
include "fof.mm"
include "forn.mm"
include "jca.mm"
include "wfn.mm"
include "ffn.mm"
include "df-fo.mm"
include "biimpri.mm"
include "sylan.mm"
include "impbii.mm"

theorem dffo2
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -onto-> B <-> ( F : A --> B /\ ran F = B ) )

  proof
    cA
    cB
    cF
    wfo
    #
    cA
    cB
    cF
    wf
    #
    cF
    crn
    cB
    wceq
    #
    wa
    @0
    @1
    @2
    cA
    cB
    cF
    fof
    cA
    cB
    cF
    forn
    jca
    @1
    cF
    cA
    wfn
    #
    @2
    @0
    cA
    cB
    cF
    ffn
    @0
    @3
    @2
    wa
    cA
    cB
    cF
    df-fo
    biimpri
    sylan
    impbii
end
