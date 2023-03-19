include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "wa.mm"
include "ccnp.mm"
include "co.mm"
include "cmap.mm"
include "cv.mm"
include "wf.mm"
include "ccnv.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "simplrl.mm"
include "simpll3.mm"
include "snidg.mm"
include "syl.mm"
include "simprr.mm"
include "wfn.mm"
include "wb.mm"
include "simplrr.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "mpbir2and.mm"
include "snssd.mm"
include "wceq.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "expr.mm"
include "ralrimiva.mm"
include "pm4.71d.mm"
include "simpl2.mm"
include "toponmax.mm"
include "simpl1.mm"
include "elmapd.mm"
include "iscnp3.mm"
include "adantr.mm"
include "3bitr4rd.mm"
include "eqrdv.mm"

theorem cnpdis
  let cA: class A
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cV: class V


  assert |- ( ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) /\ A e. X ) /\ { A } e. J ) -> ( ( J CnP K ) ` A ) = ( Y ^m X ) )

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
    cA
    cX
    wcel
    #
    w3a
    #
    cA
    csn
    #
    cJ
    wcel
    #
    wa
    #
    vf
    cA
    cJ
    cK
    ccnp
    co
    cfv
    #
    cY
    cX
    cmap
    co
    #
    @6
    cX
    cY
    vf
    cv
    #
    wf
    #
    @10
    cA
    @9
    cfv
    vx
    cv
    #
    wcel
    #
    cA
    vy
    cv
    #
    wcel
    #
    @13
    @9
    ccnv
    @11
    cima
    #
    wss
    #
    wa
    #
    vy
    cJ
    wrex
    #
    wi
    #
    vx
    cK
    wral
    #
    wa
    #
    @9
    @8
    wcel
    @9
    @7
    wcel
    #
    @6
    @10
    @20
    @3
    @5
    @10
    @20
    @3
    @5
    @10
    wa
    #
    wa
    #
    @19
    vx
    cK
    @24
    @11
    cK
    wcel
    #
    @12
    @18
    @24
    @25
    @12
    wa
    #
    wa
    #
    @5
    cA
    @4
    wcel
    #
    @4
    @15
    wss
    #
    @18
    @3
    @5
    @10
    @26
    simplrl
    @27
    @2
    @28
    @0
    @1
    @2
    @23
    @26
    simpll3
    #
    cA
    cX
    snidg
    syl
    @27
    cA
    @15
    @27
    cA
    @15
    wcel
    #
    @2
    @12
    @30
    @24
    @25
    @12
    simprr
    @27
    @10
    @9
    cX
    wfn
    @31
    @2
    @12
    wa
    wb
    @3
    @5
    @10
    @26
    simplrr
    cX
    cY
    @9
    ffn
    cX
    cA
    @11
    @9
    elpreima
    3syl
    mpbir2and
    snssd
    @17
    @28
    @29
    wa
    vy
    @4
    cJ
    @13
    @4
    wceq
    @14
    @28
    @16
    @29
    @13
    @4
    cA
    eleq2
    @13
    @4
    @15
    sseq1
    anbi12d
    rspcev
    syl12anc
    expr
    ralrimiva
    expr
    pm4.71d
    @6
    cY
    cX
    @9
    cK
    cJ
    @6
    @1
    cY
    cK
    wcel
    @0
    @1
    @2
    @5
    simpl2
    cY
    cK
    toponmax
    syl
    @6
    @0
    cX
    cJ
    wcel
    @0
    @1
    @2
    @5
    simpl1
    cX
    cJ
    toponmax
    syl
    elmapd
    @3
    @22
    @21
    wb
    @5
    vy
    vx
    cA
    @9
    cJ
    cK
    cX
    cY
    iscnp3
    adantr
    3bitr4rd
    eqrdv
end
