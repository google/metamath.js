include "con0.mm"
include "wcel.mm"
include "c1o.mm"
include "csn.mm"
include "cxp.mm"
include "cdm.mm"
include "c2o.mm"
include "cpr.mm"
include "wf.mm"
include "csur.mm"
include "1on.mm"
include "elexi.mm"
include "prid1.mm"
include "fconst6.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "snnz.mm"
include "dmxp.mm"
include "ax-mp.mm"
include "feq2i.mm"
include "mpbir.mm"
include "a1i.mm"
include "eleq1i.mm"
include "biimpri.mm"
include "elno3.mm"
include "sylanbrc.mm"

theorem noxp1o
  let cA: class A


  assert |- ( A e. On -> ( A X. { 1o } ) e. No )

  proof
    cA
    con0
    wcel
    #
    cA
    c1o
    csn
    #
    cxp
    #
    cdm
    #
    c1o
    c2o
    cpr
    #
    @2
    wf
    #
    @3
    con0
    wcel
    #
    @2
    csur
    wcel
    @5
    @0
    @5
    cA
    @4
    @2
    wf
    cA
    c1o
    @4
    c1o
    c2o
    c1o
    con0
    1on
    elexi
    #
    prid1
    fconst6
    @3
    cA
    @4
    @2
    @1
    c0
    wne
    @3
    cA
    wceq
    c1o
    @7
    snnz
    cA
    @1
    dmxp
    ax-mp
    #
    feq2i
    mpbir
    a1i
    @6
    @0
    @3
    cA
    con0
    @8
    eleq1i
    biimpri
    @2
    elno3
    sylanbrc
end
