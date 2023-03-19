include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "crn.mm"
include "ccnv.mm"
include "cdm.mm"
include "df-rn.mm"
include "cnvtrclfv.mm"
include "dmeqd.mm"
include "cvv.mm"
include "wceq.mm"
include "cnvexg.mm"
include "dmtrclfv.mm"
include "syl.mm"
include "syl6eqr.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem rntrclfvRP
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ran ( t+ ` R ) = ran R )

  proof
    cR
    cV
    wcel
    #
    cR
    ctcl
    cfv
    #
    crn
    @1
    ccnv
    #
    cdm
    #
    cR
    crn
    #
    @1
    df-rn
    @0
    @3
    cR
    ccnv
    #
    ctcl
    cfv
    #
    cdm
    #
    @4
    @0
    @2
    @6
    cR
    cV
    cnvtrclfv
    dmeqd
    @0
    @7
    @5
    cdm
    #
    @4
    @0
    @5
    cvv
    wcel
    @7
    @8
    wceq
    cR
    cV
    cnvexg
    @5
    cvv
    dmtrclfv
    syl
    cR
    df-rn
    syl6eqr
    eqtrd
    syl5eq
end
