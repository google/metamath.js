include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "cxp.mm"
include "ccn.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "ccnp.mm"
include "wral.mm"
include "fconst6g.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "adantr.mm"
include "wceq.mm"
include "simpll3.mm"
include "simplr.mm"
include "fvconst2g.mm"
include "syl2anc.mm"
include "eleq1d.mm"
include "simpll1.mm"
include "toponmax.mm"
include "syl.mm"
include "cres.mm"
include "crn.mm"
include "df-ima.mm"
include "ssid.mm"
include "xpssres.mm"
include "ax-mp.mm"
include "rneqi.mm"
include "rnxpss.mm"
include "eqsstri.mm"
include "simprr.mm"
include "snssd.mm"
include "syl5ss.mm"
include "syl5eqss.mm"
include "eleq2.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "expr.mm"
include "sylbid.mm"
include "ralrimiva.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "iscnp.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "cncnp.mm"
include "3adant3.mm"

theorem cnconst2
  let cB: class B
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) /\ B e. Y ) -> ( X X. { B } ) e. ( J Cn K ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cB
    cY
    wcel
    #
    w3a
    #
    cX
    cB
    csn
    #
    cxp
    #
    cJ
    cK
    ccn
    co
    wcel
    #
    cX
    cY
    @5
    wf
    #
    @5
    vx
    cv
    #
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    vx
    cX
    wral
    #
    @2
    @0
    @7
    @1
    cX
    cB
    cY
    fconst6g
    3ad2ant3
    #
    @3
    @9
    vx
    cX
    @3
    @8
    cX
    wcel
    #
    wa
    #
    @9
    @7
    @8
    @5
    cfv
    #
    vy
    cv
    #
    wcel
    #
    @8
    vu
    cv
    #
    wcel
    #
    @5
    @17
    cima
    #
    @15
    wss
    #
    wa
    #
    vu
    cJ
    wrex
    #
    wi
    #
    vy
    cK
    wral
    #
    @3
    @7
    @12
    @11
    adantr
    @13
    @23
    vy
    cK
    @13
    @15
    cK
    wcel
    #
    wa
    #
    @16
    cB
    @15
    wcel
    #
    @22
    @26
    @14
    cB
    @15
    @26
    @2
    @12
    @14
    cB
    wceq
    @0
    @1
    @2
    @12
    @25
    simpll3
    @3
    @12
    @25
    simplr
    cX
    cB
    @8
    cY
    fvconst2g
    syl2anc
    eleq1d
    @13
    @25
    @27
    @22
    @13
    @25
    @27
    wa
    #
    wa
    #
    cX
    cJ
    wcel
    #
    @12
    @5
    cX
    cima
    #
    @15
    wss
    #
    @22
    @29
    @0
    @30
    @0
    @1
    @2
    @12
    @28
    simpll1
    cX
    cJ
    toponmax
    syl
    @3
    @12
    @28
    simplr
    @29
    @31
    @5
    cX
    cres
    #
    crn
    #
    @15
    @5
    cX
    df-ima
    @29
    @34
    @4
    @15
    @34
    @5
    crn
    @4
    @33
    @5
    cX
    cX
    wss
    @33
    @5
    wceq
    cX
    ssid
    cX
    @4
    cX
    xpssres
    ax-mp
    rneqi
    cX
    @4
    rnxpss
    eqsstri
    @29
    cB
    @15
    @13
    @25
    @27
    simprr
    snssd
    syl5ss
    syl5eqss
    @21
    @12
    @32
    wa
    vu
    cX
    cJ
    @17
    cX
    wceq
    #
    @18
    @12
    @20
    @32
    @17
    cX
    @8
    eleq2
    @35
    @19
    @31
    @15
    @17
    cX
    @5
    imaeq2
    sseq1d
    anbi12d
    rspcev
    syl12anc
    expr
    sylbid
    ralrimiva
    @13
    @0
    @1
    @12
    @9
    @7
    @24
    wa
    wb
    @0
    @1
    @2
    @12
    simpl1
    @0
    @1
    @2
    @12
    simpl2
    @3
    @12
    simpr
    vu
    vy
    @8
    @5
    cJ
    cK
    cX
    cY
    iscnp
    syl3anc
    mpbir2and
    ralrimiva
    @0
    @1
    @6
    @7
    @10
    wa
    wb
    @2
    vx
    @5
    cJ
    cK
    cX
    cY
    cncnp
    3adant3
    mpbir2and
end
