include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "cnei.mm"
include "cfv.mm"
include "cxp.mm"
include "ctx.mm"
include "co.mm"
include "cuni.mm"
include "wss.mm"
include "cv.mm"
include "wrex.mm"
include "neii1.mm"
include "ad2ant2r.mm"
include "ad2ant2l.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "wceq.mm"
include "txuni.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "simp-5l.mm"
include "simp-4r.mm"
include "simplr.mm"
include "txopn.mm"
include "syl12anc.mm"
include "simpr1l.mm"
include "3anassrs.mm"
include "simprl.mm"
include "simpr1r.mm"
include "simprr.mm"
include "sseq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "neii2.mm"
include "ad2antrr.mm"
include "r19.29a.mm"
include "wb.mm"
include "txtop.mm"
include "neiss2.mm"
include "eqid.mm"
include "isnei.mm"
include "mpbir2and.mm"

theorem neitx
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume neitx.x: |- X = U. J
  assume neitx.y: |- Y = U. K


  assert |- ( ( ( J e. Top /\ K e. Top ) /\ ( A e. ( ( nei ` J ) ` C ) /\ B e. ( ( nei ` K ) ` D ) ) ) -> ( A X. B ) e. ( ( nei ` ( J tX K ) ) ` ( C X. D ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    wa
    #
    cA
    cC
    cJ
    cnei
    cfv
    cfv
    wcel
    #
    cB
    cD
    cK
    cnei
    cfv
    cfv
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cxp
    #
    cC
    cD
    cxp
    #
    cJ
    cK
    ctx
    co
    #
    cnei
    cfv
    cfv
    wcel
    #
    @7
    @9
    cuni
    #
    wss
    #
    @8
    vc
    cv
    #
    wss
    #
    @13
    @7
    wss
    #
    wa
    #
    vc
    @9
    wrex
    #
    @6
    @7
    cX
    cY
    cxp
    #
    @11
    @6
    cA
    cX
    wss
    #
    cB
    cY
    wss
    #
    @7
    @18
    wss
    @0
    @3
    @19
    @1
    @4
    cC
    cJ
    cA
    cX
    neitx.x
    neii1
    ad2ant2r
    @1
    @4
    @20
    @0
    @3
    cD
    cK
    cB
    cY
    neitx.y
    neii1
    ad2ant2l
    cA
    cX
    cB
    cY
    xpss12
    syl2anc
    @2
    @18
    @11
    wceq
    @5
    cJ
    cK
    cX
    cY
    neitx.x
    neitx.y
    txuni
    adantr
    #
    sseqtrd
    @6
    cC
    va
    cv
    #
    wss
    #
    @22
    cA
    wss
    #
    wa
    #
    @17
    va
    cJ
    @6
    @22
    cJ
    wcel
    #
    wa
    #
    @25
    wa
    #
    cD
    vb
    cv
    #
    wss
    #
    @29
    cB
    wss
    #
    wa
    #
    @17
    vb
    cK
    @28
    @29
    cK
    wcel
    #
    wa
    #
    @32
    wa
    #
    @22
    @29
    cxp
    #
    @9
    wcel
    #
    @8
    @36
    wss
    #
    @36
    @7
    wss
    #
    @17
    @35
    @2
    @26
    @33
    @37
    @2
    @5
    @26
    @25
    @33
    @32
    simp-5l
    @6
    @26
    @25
    @33
    @32
    simp-4r
    @28
    @33
    @32
    simplr
    @22
    @29
    cJ
    cK
    ctop
    ctop
    txopn
    syl12anc
    @35
    @23
    @30
    @38
    @27
    @25
    @33
    @32
    @23
    @23
    @24
    @33
    @32
    @27
    simpr1l
    3anassrs
    @34
    @30
    @31
    simprl
    cC
    @22
    cD
    @29
    xpss12
    syl2anc
    @35
    @24
    @31
    @39
    @27
    @25
    @33
    @32
    @24
    @23
    @24
    @33
    @32
    @27
    simpr1r
    3anassrs
    @34
    @30
    @31
    simprr
    @22
    cA
    @29
    cB
    xpss12
    syl2anc
    @16
    @38
    @39
    wa
    vc
    @36
    @9
    @13
    @36
    wceq
    @14
    @38
    @15
    @39
    @13
    @36
    @8
    sseq2
    @13
    @36
    @7
    sseq1
    anbi12d
    rspcev
    syl12anc
    @6
    @32
    vb
    cK
    wrex
    #
    @26
    @25
    @1
    @4
    @40
    @0
    @3
    cD
    vb
    cK
    cB
    neii2
    ad2ant2l
    ad2antrr
    r19.29a
    @0
    @3
    @25
    va
    cJ
    wrex
    @1
    @4
    cC
    va
    cJ
    cA
    neii2
    ad2ant2r
    r19.29a
    @6
    @9
    ctop
    wcel
    #
    @8
    @11
    wss
    @10
    @12
    @17
    wa
    wb
    @2
    @41
    @5
    cJ
    cK
    txtop
    adantr
    @6
    @8
    @18
    @11
    @6
    cC
    cX
    wss
    #
    cD
    cY
    wss
    #
    @8
    @18
    wss
    @0
    @3
    @42
    @1
    @4
    cC
    cJ
    cA
    cX
    neitx.x
    neiss2
    ad2ant2r
    @1
    @4
    @43
    @0
    @3
    cD
    cK
    cB
    cY
    neitx.y
    neiss2
    ad2ant2l
    cC
    cX
    cD
    cY
    xpss12
    syl2anc
    @21
    sseqtrd
    @8
    vc
    @9
    @7
    @11
    @11
    eqid
    isnei
    syl2anc
    mpbir2and
end
