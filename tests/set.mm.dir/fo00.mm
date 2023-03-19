include "c0.mm"
include "wfo.mm"
include "wf1o.mm"
include "wceq.mm"
include "wa.mm"
include "wf1.mm"
include "wfn.mm"
include "fofn.mm"
include "fn0.mm"
include "f10.mm"
include "f1eq1.mm"
include "mpbiri.mm"
include "sylbi.mm"
include "syl.mm"
include "ancri.mm"
include "df-f1o.mm"
include "sylibr.mm"
include "f1ofo.mm"
include "impbii.mm"
include "f1o00.mm"
include "bitri.mm"

theorem fo00
  let cA: class A
  let cF: class F


  assert |- ( F : (/) -onto-> A <-> ( F = (/) /\ A = (/) ) )

  proof
    c0
    cA
    cF
    wfo
    #
    c0
    cA
    cF
    wf1o
    #
    cF
    c0
    wceq
    #
    cA
    c0
    wceq
    wa
    @0
    @1
    @0
    c0
    cA
    cF
    wf1
    #
    @0
    wa
    @1
    @0
    @3
    @0
    cF
    c0
    wfn
    #
    @3
    c0
    cA
    cF
    fofn
    @4
    @2
    @3
    cF
    fn0
    @2
    @3
    c0
    cA
    c0
    wf1
    cA
    f10
    c0
    cA
    cF
    c0
    f1eq1
    mpbiri
    sylbi
    syl
    ancri
    c0
    cA
    cF
    df-f1o
    sylibr
    c0
    cA
    cF
    f1ofo
    impbii
    cA
    cF
    f1o00
    bitri
end
