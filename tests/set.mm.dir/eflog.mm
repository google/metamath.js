include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "clog.mm"
include "cfv.mm"
include "ce.mm"
include "crn.mm"
include "cres.mm"
include "ccnv.mm"
include "dflog2.mm"
include "fveq1i.mm"
include "fveq2i.mm"
include "wceq.mm"
include "logrncl.mm"
include "fvres.mm"
include "syl.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "wf1o.mm"
include "eff1o2.mm"
include "f1ocnvfv2.mm"
include "mpan.mm"
include "sylbir.mm"
include "3eqtr3a.mm"

theorem eflog
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( exp ` ( log ` A ) ) = A )

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    wa
    #
    cA
    clog
    cfv
    #
    ce
    clog
    crn
    #
    cres
    #
    cfv
    #
    cA
    @3
    ccnv
    #
    cfv
    #
    @3
    cfv
    #
    @1
    ce
    cfv
    #
    cA
    @1
    @6
    @3
    cA
    clog
    @5
    dflog2
    fveq1i
    fveq2i
    @0
    @1
    @2
    wcel
    @4
    @8
    wceq
    cA
    logrncl
    @1
    @2
    ce
    fvres
    syl
    @0
    cA
    cc
    cc0
    csn
    cdif
    #
    wcel
    #
    @7
    cA
    wceq
    #
    cA
    cc
    cc0
    eldifsn
    @2
    @9
    @3
    wf1o
    @10
    @11
    eff1o2
    @2
    @9
    cA
    @3
    f1ocnvfv2
    mpan
    sylbir
    3eqtr3a
end
