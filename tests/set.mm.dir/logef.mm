include "clog.mm"
include "crn.mm"
include "wcel.mm"
include "ce.mm"
include "cres.mm"
include "cfv.mm"
include "ccnv.mm"
include "dflog2.mm"
include "fveq1i.mm"
include "fvres.mm"
include "fveq2d.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wf1o.mm"
include "wceq.mm"
include "eff1o2.mm"
include "f1ocnvfv1.mm"
include "mpan.mm"
include "3eqtr3a.mm"

theorem logef
  let cA: class A


  assert |- ( A e. ran log -> ( log ` ( exp ` A ) ) = A )

  proof
    cA
    clog
    crn
    #
    wcel
    #
    cA
    ce
    @0
    cres
    #
    cfv
    #
    clog
    cfv
    @3
    @2
    ccnv
    #
    cfv
    #
    cA
    ce
    cfv
    #
    clog
    cfv
    cA
    @3
    clog
    @4
    dflog2
    fveq1i
    @1
    @3
    @6
    clog
    cA
    @0
    ce
    fvres
    fveq2d
    @0
    cc
    cc0
    csn
    cdif
    #
    @2
    wf1o
    @1
    @5
    cA
    wceq
    eff1o2
    @0
    @7
    cA
    @2
    f1ocnvfv1
    mpan
    3eqtr3a
end
