include "cperf.mm"
include "wcel.mm"
include "wa.mm"
include "ctop.mm"
include "cv.mm"
include "csn.mm"
include "wn.mm"
include "cuni.mm"
include "wral.mm"
include "ctopon.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "wss.mm"
include "perftop.mm"
include "adantr.mm"
include "toptopon.mm"
include "sylib.mm"
include "elssuni.mm"
include "adantl.mm"
include "syl6sseqr.mm"
include "resttopon.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "topontop.mm"
include "syl.mm"
include "sselda.mm"
include "perfi.mm"
include "adantlr.mm"
include "syldan.mm"
include "eleq2i.mm"
include "wb.mm"
include "restopn2.mm"
include "sylan.mm"
include "simpl.mm"
include "syl6bi.mm"
include "syl5bi.mm"
include "mtod.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "toponuni.mm"
include "raleqdv.mm"
include "mpbid.mm"
include "eqid.mm"
include "isperf3.mm"
include "sylanbrc.mm"

theorem perfopn
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vo: setvar o
  let vx: setvar x
  let cS: class S
  assume restcls.1: |- X = U. J
  assume restcls.2: |- K = ( J |`t Y )


  assert |- ( ( J e. Perf /\ Y e. J ) -> K e. Perf )

  proof
    cJ
    cperf
    wcel
    #
    cY
    cJ
    wcel
    #
    wa
    #
    cK
    ctop
    wcel
    #
    vx
    cv
    #
    csn
    #
    cK
    wcel
    #
    wn
    #
    vx
    cK
    cuni
    #
    wral
    #
    cK
    cperf
    wcel
    @2
    cK
    cY
    ctopon
    cfv
    #
    wcel
    #
    @3
    @2
    cK
    cJ
    cY
    crest
    co
    #
    @10
    restcls.2
    @2
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cY
    cX
    wss
    @12
    @10
    wcel
    @2
    cJ
    ctop
    wcel
    #
    @13
    @0
    @14
    @1
    cJ
    perftop
    #
    adantr
    cJ
    cX
    restcls.1
    toptopon
    sylib
    @2
    cY
    cJ
    cuni
    #
    cX
    @1
    cY
    @16
    wss
    @0
    cY
    cJ
    elssuni
    adantl
    restcls.1
    syl6sseqr
    #
    cY
    cJ
    cX
    resttopon
    syl2anc
    syl5eqel
    #
    cY
    cK
    topontop
    syl
    @2
    @7
    vx
    cY
    wral
    @9
    @2
    @7
    vx
    cY
    @2
    @4
    cY
    wcel
    #
    wa
    #
    @6
    @5
    cJ
    wcel
    #
    @2
    @19
    @4
    cX
    wcel
    #
    @21
    wn
    #
    @2
    cY
    cX
    @4
    @17
    sselda
    @0
    @22
    @23
    @1
    @4
    cJ
    cX
    restcls.1
    perfi
    adantlr
    syldan
    @6
    @5
    @12
    wcel
    #
    @20
    @21
    cK
    @12
    @5
    restcls.2
    eleq2i
    @20
    @24
    @21
    @5
    cY
    wss
    #
    wa
    #
    @21
    @2
    @24
    @26
    wb
    #
    @19
    @0
    @14
    @1
    @27
    @15
    cY
    @5
    cJ
    restopn2
    sylan
    adantr
    @21
    @25
    simpl
    syl6bi
    syl5bi
    mtod
    ralrimiva
    @2
    @7
    vx
    cY
    @8
    @2
    @11
    cY
    @8
    wceq
    @18
    cY
    cK
    toponuni
    syl
    raleqdv
    mpbid
    vx
    cK
    @8
    @8
    eqid
    isperf3
    sylanbrc
end
