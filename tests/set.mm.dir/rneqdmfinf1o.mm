include "cfn.mm"
include "wcel.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "w3a.mm"
include "wfo.mm"
include "cen.mm"
include "wbr.mm"
include "wf1o.mm"
include "dffn4.mm"
include "biimpi.mm"
include "3ad2ant2.mm"
include "wb.mm"
include "foeq3.mm"
include "3ad2ant3.mm"
include "mpbid.mm"
include "enrefg.mm"
include "3ad2ant1.mm"
include "simp1.mm"
include "fofinf1o.mm"
include "syl3anc.mm"

theorem rneqdmfinf1o
  let cA: class A
  let cF: class F


  assert |- ( ( A e. Fin /\ F Fn A /\ ran F = A ) -> F : A -1-1-onto-> A )

  proof
    cA
    cfn
    wcel
    #
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cA
    wceq
    #
    w3a
    #
    cA
    cA
    cF
    wfo
    #
    cA
    cA
    cen
    wbr
    #
    @0
    cA
    cA
    cF
    wf1o
    @4
    cA
    @2
    cF
    wfo
    #
    @5
    @1
    @0
    @7
    @3
    @1
    @7
    cA
    cF
    dffn4
    biimpi
    3ad2ant2
    @3
    @0
    @7
    @5
    wb
    @1
    @2
    cA
    cA
    cF
    foeq3
    3ad2ant3
    mpbid
    @0
    @1
    @6
    @3
    cA
    cfn
    enrefg
    3ad2ant1
    @0
    @1
    @3
    simp1
    cA
    cA
    cF
    fofinf1o
    syl3anc
end
