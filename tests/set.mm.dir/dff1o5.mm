include "wf1o.mm"
include "wf1.mm"
include "wfo.mm"
include "wa.mm"
include "crn.mm"
include "wceq.mm"
include "df-f1o.mm"
include "wf.mm"
include "f1f.mm"
include "biantrurd.mm"
include "dffo2.mm"
include "syl6rbbr.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem dff1o5
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-onto-> B <-> ( F : A -1-1-> B /\ ran F = B ) )

  proof
    cA
    cB
    cF
    wf1o
    cA
    cB
    cF
    wf1
    #
    cA
    cB
    cF
    wfo
    #
    wa
    @0
    cF
    crn
    cB
    wceq
    #
    wa
    cA
    cB
    cF
    df-f1o
    @0
    @1
    @2
    @0
    @2
    cA
    cB
    cF
    wf
    #
    @2
    wa
    @1
    @0
    @3
    @2
    cA
    cB
    cF
    f1f
    biantrurd
    cA
    cB
    cF
    dffo2
    syl6rbbr
    pm5.32i
    bitri
end
