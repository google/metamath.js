include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cun.mm"
include "wss.mm"
include "trclfvub.mm"
include "dmss.mm"
include "syl.mm"
include "dmun.mm"
include "wceq.mm"
include "c0.mm"
include "dm0rn0.mm"
include "xpeq1.mm"
include "0xp.mm"
include "syl6eq.mm"
include "dmeqd.mm"
include "dm0.mm"
include "a1i.mm"
include "eqcom.mm"
include "biimpi.mm"
include "3eqtrd.mm"
include "sylbir.mm"
include "dmxp.mm"
include "pm2.61ine.mm"
include "uneq2i.mm"
include "unidm.mm"
include "3eqtri.mm"
include "syl6sseq.mm"
include "trclfvlb.mm"
include "eqssd.mm"

theorem dmtrclfv
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
    #
    cR
    cdm
    #
    @0
    @2
    cR
    @3
    cR
    crn
    #
    cxp
    #
    cun
    #
    cdm
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
    dmss
    syl
    @7
    @3
    @5
    cdm
    #
    cun
    @3
    @3
    cun
    @3
    cR
    @5
    dmun
    @8
    @3
    @3
    @8
    @3
    wceq
    #
    @4
    c0
    @4
    c0
    wceq
    @3
    c0
    wceq
    #
    @9
    cR
    dm0rn0
    @10
    @8
    c0
    cdm
    #
    c0
    @3
    @10
    @5
    c0
    @10
    @5
    c0
    @4
    cxp
    c0
    @3
    c0
    @4
    xpeq1
    @4
    0xp
    syl6eq
    dmeqd
    @11
    c0
    wceq
    @10
    dm0
    a1i
    @10
    c0
    @3
    wceq
    @3
    c0
    eqcom
    biimpi
    3eqtrd
    sylbir
    @3
    @4
    dmxp
    pm2.61ine
    uneq2i
    @3
    unidm
    3eqtri
    syl6sseq
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
    dmss
    syl
    eqssd
end
