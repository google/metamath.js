include "wcel.mm"
include "wrel.mm"
include "wa.mm"
include "ctcl.mm"
include "cfv.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "trclfvub.mm"
include "adantr.mm"
include "wceq.mm"
include "simpr.mm"
include "relssdmrn.mm"
include "ssequn1.mm"
include "biimpi.mm"
include "3syl.mm"
include "sseqtrd.mm"
include "xpss.mm"
include "syl6ss.mm"
include "df-rel.mm"
include "sylibr.mm"

theorem reltrclfv
  let cR: class R
  let cV: class V


  assert |- ( ( R e. V /\ Rel R ) -> Rel ( t+ ` R ) )

  proof
    cR
    cV
    wcel
    #
    cR
    wrel
    #
    wa
    #
    cR
    ctcl
    cfv
    #
    cvv
    cvv
    cxp
    #
    wss
    @3
    wrel
    @2
    @3
    cR
    cdm
    #
    cR
    crn
    #
    cxp
    #
    @4
    @2
    @3
    cR
    @7
    cun
    #
    @7
    @0
    @3
    @8
    wss
    @1
    cR
    cV
    trclfvub
    adantr
    @2
    @1
    cR
    @7
    wss
    #
    @8
    @7
    wceq
    #
    @0
    @1
    simpr
    cR
    relssdmrn
    @9
    @10
    cR
    @7
    ssequn1
    biimpi
    3syl
    sseqtrd
    @5
    @6
    xpss
    syl6ss
    @3
    df-rel
    sylibr
end
