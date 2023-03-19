include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "ccnp.mm"
include "cfv.mm"
include "cuni.mm"
include "wf.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "eqid.mm"
include "cnf.mm"
include "adantr.mm"
include "cnima.mm"
include "ad2ant2r.mm"
include "simpr.mm"
include "simprr.mm"
include "wfn.mm"
include "wb.mm"
include "ad2antrr.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "mpbir2and.mm"
include "wceq.mm"
include "eqimss.mm"
include "biantrud.mm"
include "eleq2.mm"
include "bitr3d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "expr.mm"
include "ralrimiva.mm"
include "ctopon.mm"
include "ctop.mm"
include "cntop1.mm"
include "toptopon.mm"
include "sylib.mm"
include "cntop2.mm"
include "iscnp3.mm"
include "syl3anc.mm"

theorem cncnpi
  let cA: class A
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cP: class P
  assume cnsscnp.1: |- X = U. J


  assert |- ( ( F e. ( J Cn K ) /\ A e. X ) -> F e. ( ( J CnP K ) ` A ) )

  proof
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cF
    cA
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    cX
    cK
    cuni
    #
    cF
    wf
    #
    cA
    cF
    cfv
    vy
    cv
    #
    wcel
    #
    cA
    vx
    cv
    #
    wcel
    #
    @8
    cF
    ccnv
    @6
    cima
    #
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    wi
    #
    vy
    cK
    wral
    #
    @0
    @5
    @1
    cF
    cJ
    cK
    cX
    @4
    cnsscnp.1
    @4
    eqid
    #
    cnf
    #
    adantr
    @2
    @14
    vy
    cK
    @2
    @6
    cK
    wcel
    #
    @7
    @13
    @2
    @18
    @7
    wa
    #
    wa
    #
    @10
    cJ
    wcel
    #
    cA
    @10
    wcel
    #
    @13
    @0
    @18
    @21
    @1
    @7
    @6
    cF
    cJ
    cK
    cnima
    ad2ant2r
    @20
    @22
    @1
    @7
    @2
    @1
    @19
    @0
    @1
    simpr
    #
    adantr
    @2
    @18
    @7
    simprr
    @20
    @5
    cF
    cX
    wfn
    @22
    @1
    @7
    wa
    wb
    @0
    @5
    @1
    @19
    @17
    ad2antrr
    cX
    @4
    cF
    ffn
    cX
    cA
    @6
    cF
    elpreima
    3syl
    mpbir2and
    @12
    @22
    vx
    @10
    cJ
    @8
    @10
    wceq
    #
    @9
    @12
    @22
    @24
    @11
    @9
    @8
    @10
    eqimss
    biantrud
    @8
    @10
    cA
    eleq2
    bitr3d
    rspcev
    syl2anc
    expr
    ralrimiva
    @2
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    @4
    ctopon
    cfv
    wcel
    #
    @1
    @3
    @5
    @15
    wa
    wb
    @2
    cJ
    ctop
    wcel
    #
    @25
    @0
    @27
    @1
    cF
    cJ
    cK
    cntop1
    adantr
    cJ
    cX
    cnsscnp.1
    toptopon
    sylib
    @2
    cK
    ctop
    wcel
    #
    @26
    @0
    @28
    @1
    cF
    cJ
    cK
    cntop2
    adantr
    cK
    @4
    @16
    toptopon
    sylib
    @23
    vx
    vy
    cA
    cF
    cJ
    cK
    cX
    @4
    iscnp3
    syl3anc
    mpbir2and
end
