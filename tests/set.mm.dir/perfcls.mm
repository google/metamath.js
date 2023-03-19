include "ct1.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "clp.mm"
include "cfv.mm"
include "ccl.mm"
include "crest.mm"
include "co.mm"
include "cperf.mm"
include "lpcls.mm"
include "sseq2d.mm"
include "cun.mm"
include "ctop.mm"
include "wceq.mm"
include "t1top.mm"
include "clslp.mm"
include "sylan.mm"
include "sseq1d.mm"
include "ssequn1.mm"
include "ssun2.mm"
include "eqss.mm"
include "mpbiran2.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "bitr2d.mm"
include "wb.mm"
include "eqid.mm"
include "restperf.mm"
include "clsss3.mm"
include "syldan.mm"
include "3bitr4d.mm"

theorem perfcls
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  assume lpcls.1: |- X = U. J


  assert |- ( ( J e. Fre /\ S C_ X ) -> ( ( J |`t S ) e. Perf <-> ( J |`t ( ( cls ` J ) ` S ) ) e. Perf ) )

  proof
    cJ
    ct1
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cS
    cS
    cJ
    clp
    cfv
    #
    cfv
    #
    wss
    #
    cS
    cJ
    ccl
    cfv
    cfv
    #
    @6
    @3
    cfv
    #
    wss
    #
    cJ
    cS
    crest
    co
    #
    cperf
    wcel
    #
    cJ
    @6
    crest
    co
    #
    cperf
    wcel
    #
    @2
    @8
    @6
    @4
    wss
    #
    @5
    @2
    @7
    @4
    @6
    cS
    cJ
    cX
    lpcls.1
    lpcls
    sseq2d
    @2
    @13
    cS
    @4
    cun
    #
    @4
    wss
    #
    @5
    @2
    @6
    @14
    @4
    @0
    cJ
    ctop
    wcel
    #
    @1
    @6
    @14
    wceq
    cJ
    t1top
    #
    cS
    cJ
    cX
    lpcls.1
    clslp
    sylan
    sseq1d
    @5
    @14
    @4
    wceq
    #
    @15
    cS
    @4
    ssequn1
    @18
    @15
    @4
    @14
    wss
    @4
    cS
    ssun2
    @14
    @4
    eqss
    mpbiran2
    bitri
    syl6bbr
    bitr2d
    @0
    @16
    @1
    @10
    @5
    wb
    @17
    cJ
    @9
    cX
    cS
    lpcls.1
    @9
    eqid
    restperf
    sylan
    @0
    @16
    @1
    @12
    @8
    wb
    #
    @17
    @16
    @1
    @6
    cX
    wss
    @19
    cS
    cJ
    cX
    lpcls.1
    clsss3
    cJ
    @11
    cX
    @6
    lpcls.1
    @11
    eqid
    restperf
    syldan
    sylan
    3bitr4d
end
