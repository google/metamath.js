include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "crn.mm"
include "cdm.mm"
include "cxp.mm"
include "cun.mm"
include "wss.mm"
include "trclfvub.mm"
include "rnss.mm"
include "syl.mm"
include "wceq.mm"
include "rnun.mm"
include "a1i.mm"
include "rnxpss.mm"
include "ssequn2.mm"
include "mpbi.mm"
include "syl6eq.mm"
include "sseqtrd.mm"
include "trclfvlb.mm"
include "eqssd.mm"

theorem rntrclfvOAI
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
    #
    cR
    crn
    #
    @0
    @2
    cR
    cR
    cdm
    #
    @3
    cxp
    #
    cun
    #
    crn
    #
    @3
    @0
    @1
    @6
    wss
    @2
    @7
    wss
    cR
    cV
    trclfvub
    @1
    @6
    rnss
    syl
    @0
    @7
    @3
    @5
    crn
    #
    cun
    #
    @3
    @7
    @9
    wceq
    @0
    cR
    @5
    rnun
    a1i
    @8
    @3
    wss
    @9
    @3
    wceq
    @4
    @3
    rnxpss
    @8
    @3
    ssequn2
    mpbi
    syl6eq
    sseqtrd
    @0
    cR
    @1
    wss
    @3
    @2
    wss
    cR
    cV
    trclfvlb
    cR
    @1
    rnss
    syl
    eqssd
end
