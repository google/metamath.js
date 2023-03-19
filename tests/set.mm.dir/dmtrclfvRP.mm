include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "cdm.mm"
include "ccom.mm"
include "cun.mm"
include "trclfvdecomr.mm"
include "dmeqd.mm"
include "dmun.mm"
include "wss.mm"
include "wceq.mm"
include "dmcoss.mm"
include "ssequn2.mm"
include "mpbi.mm"
include "eqtri.mm"
include "syl6eq.mm"

theorem dmtrclfvRP
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> dom ( t+ ` R ) = dom R )

  proof
    cR
    cV
    wcel
    #
    cR
    ctcl
    cfv
    #
    cdm
    cR
    @1
    cR
    ccom
    #
    cun
    #
    cdm
    #
    cR
    cdm
    #
    @0
    @1
    @3
    cR
    cV
    trclfvdecomr
    dmeqd
    @4
    @5
    @2
    cdm
    #
    cun
    #
    @5
    cR
    @2
    dmun
    @6
    @5
    wss
    @7
    @5
    wceq
    @1
    cR
    dmcoss
    @6
    @5
    ssequn2
    mpbi
    eqtri
    syl6eq
end
