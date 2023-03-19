include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "ctx.mm"
include "co.mm"
include "ccmp.mm"
include "cuni.mm"
include "c1st.mm"
include "cxp.mm"
include "cres.mm"
include "wfo.mm"
include "ccn.mm"
include "simpr.mm"
include "simplrr.mm"
include "fo1stres.mm"
include "syl.mm"
include "wceq.mm"
include "wb.mm"
include "txuni.mm"
include "ad2antrr.mm"
include "foeq2.mm"
include "mpbid.mm"
include "ctopon.mm"
include "cfv.mm"
include "toptopon.mm"
include "tx1cn.mm"
include "syl2anb.mm"
include "cncmp.mm"
include "syl3anc.mm"
include "c2nd.mm"
include "simplrl.mm"
include "fo2ndres.mm"
include "tx2cn.mm"
include "jca.mm"
include "ex.mm"
include "txcmp.mm"
include "impbid1.mm"

theorem txcmpb
  let cR: class R
  let cS: class S
  let cX: class X
  let cY: class Y
  assume txcmpb.1: |- X = U. R
  assume txcmpb.2: |- Y = U. S


  assert |- ( ( ( R e. Top /\ S e. Top ) /\ ( X =/= (/) /\ Y =/= (/) ) ) -> ( ( R tX S ) e. Comp <-> ( R e. Comp /\ S e. Comp ) ) )

  proof
    cR
    ctop
    wcel
    #
    cS
    ctop
    wcel
    #
    wa
    #
    cX
    c0
    wne
    #
    cY
    c0
    wne
    #
    wa
    #
    wa
    #
    cR
    cS
    ctx
    co
    #
    ccmp
    wcel
    #
    cR
    ccmp
    wcel
    #
    cS
    ccmp
    wcel
    #
    wa
    #
    @6
    @8
    @11
    @6
    @8
    wa
    #
    @9
    @10
    @12
    @8
    @7
    cuni
    #
    cX
    c1st
    cX
    cY
    cxp
    #
    cres
    #
    wfo
    #
    @15
    @7
    cR
    ccn
    co
    wcel
    #
    @9
    @6
    @8
    simpr
    #
    @12
    @14
    cX
    @15
    wfo
    #
    @16
    @12
    @4
    @19
    @2
    @3
    @4
    @8
    simplrr
    cX
    cY
    fo1stres
    syl
    @12
    @14
    @13
    wceq
    #
    @19
    @16
    wb
    @2
    @20
    @5
    @8
    cR
    cS
    cX
    cY
    txcmpb.1
    txcmpb.2
    txuni
    ad2antrr
    #
    @14
    @13
    cX
    @15
    foeq2
    syl
    mpbid
    @2
    @17
    @5
    @8
    @0
    cR
    cX
    ctopon
    cfv
    wcel
    #
    cS
    cY
    ctopon
    cfv
    wcel
    #
    @17
    @1
    cR
    cX
    txcmpb.1
    toptopon
    #
    cS
    cY
    txcmpb.2
    toptopon
    #
    cR
    cS
    cX
    cY
    tx1cn
    syl2anb
    ad2antrr
    @15
    @7
    cR
    @13
    cX
    txcmpb.1
    cncmp
    syl3anc
    @12
    @8
    @13
    cY
    c2nd
    @14
    cres
    #
    wfo
    #
    @26
    @7
    cS
    ccn
    co
    wcel
    #
    @10
    @18
    @12
    @14
    cY
    @26
    wfo
    #
    @27
    @12
    @3
    @29
    @2
    @3
    @4
    @8
    simplrl
    cX
    cY
    fo2ndres
    syl
    @12
    @20
    @29
    @27
    wb
    @21
    @14
    @13
    cY
    @26
    foeq2
    syl
    mpbid
    @2
    @28
    @5
    @8
    @0
    @22
    @23
    @28
    @1
    @24
    @25
    cR
    cS
    cX
    cY
    tx2cn
    syl2anb
    ad2antrr
    @26
    @7
    cS
    @13
    cY
    txcmpb.2
    cncmp
    syl3anc
    jca
    ex
    cR
    cS
    txcmp
    impbid1
end
