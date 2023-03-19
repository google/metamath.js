include "ccmp.mm"
include "wcel.mm"
include "ccn.mm"
include "co.mm"
include "wa.mm"
include "cuni.mm"
include "crn.mm"
include "crest.mm"
include "wfo.mm"
include "simpl.mm"
include "wfn.mm"
include "wf.mm"
include "eqid.mm"
include "cnf.mm"
include "adantl.mm"
include "ffn.mm"
include "syl.mm"
include "dffn4.mm"
include "sylib.mm"
include "wceq.mm"
include "wb.mm"
include "ctop.mm"
include "wss.mm"
include "cntop2.mm"
include "frn.mm"
include "restuni.mm"
include "syl2anc.mm"
include "foeq3.mm"
include "mpbid.mm"
include "simpr.mm"
include "ctopon.mm"
include "cfv.mm"
include "toptopon.mm"
include "ssid.mm"
include "a1i.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "cncmp.mm"

theorem rncmp
  let cF: class F
  let cJ: class J
  let cK: class K


  assert |- ( ( J e. Comp /\ F e. ( J Cn K ) ) -> ( K |`t ran F ) e. Comp )

  proof
    cJ
    ccmp
    wcel
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    wa
    #
    @0
    cJ
    cuni
    #
    cK
    cF
    crn
    #
    crest
    co
    #
    cuni
    #
    cF
    wfo
    #
    cF
    cJ
    @5
    ccn
    co
    wcel
    #
    @5
    ccmp
    wcel
    @0
    @1
    simpl
    @2
    @3
    @4
    cF
    wfo
    #
    @7
    @2
    cF
    @3
    wfn
    #
    @9
    @2
    @3
    cK
    cuni
    #
    cF
    wf
    #
    @10
    @1
    @12
    @0
    cF
    cJ
    cK
    @3
    @11
    @3
    eqid
    @11
    eqid
    #
    cnf
    adantl
    #
    @3
    @11
    cF
    ffn
    syl
    @3
    cF
    dffn4
    sylib
    @2
    @4
    @6
    wceq
    #
    @9
    @7
    wb
    @2
    cK
    ctop
    wcel
    #
    @4
    @11
    wss
    #
    @15
    @1
    @16
    @0
    cF
    cJ
    cK
    cntop2
    adantl
    #
    @2
    @12
    @17
    @14
    @3
    @11
    cF
    frn
    syl
    #
    @4
    cK
    @11
    @13
    restuni
    syl2anc
    @4
    @6
    @3
    cF
    foeq3
    syl
    mpbid
    @2
    @1
    @8
    @0
    @1
    simpr
    @2
    cK
    @11
    ctopon
    cfv
    wcel
    #
    @4
    @4
    wss
    #
    @17
    @1
    @8
    wb
    @2
    @16
    @20
    @18
    cK
    @11
    @13
    toptopon
    sylib
    @21
    @2
    @4
    ssid
    a1i
    @19
    @4
    cF
    cJ
    cK
    @11
    cnrest2
    syl3anc
    mpbid
    cF
    cJ
    @5
    @3
    @6
    @6
    eqid
    cncmp
    syl3anc
end
