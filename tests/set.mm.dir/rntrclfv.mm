include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "crn.mm"
include "ccom.mm"
include "cun.mm"
include "trclfvdecoml.mm"
include "rneqd.mm"
include "rnun.mm"
include "wss.mm"
include "wceq.mm"
include "rncoss.mm"
include "ssequn2.mm"
include "mpbi.mm"
include "eqtri.mm"
include "syl6eq.mm"

theorem rntrclfv
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
    cR
    cR
    @1
    ccom
    #
    cun
    #
    crn
    #
    cR
    crn
    #
    @0
    @1
    @3
    cR
    cV
    trclfvdecoml
    rneqd
    @4
    @5
    @2
    crn
    #
    cun
    #
    @5
    cR
    @2
    rnun
    @6
    @5
    wss
    @7
    @5
    wceq
    cR
    @1
    rncoss
    @6
    @5
    ssequn2
    mpbi
    eqtri
    syl6eq
end
