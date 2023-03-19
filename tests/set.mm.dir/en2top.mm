include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "c0.mm"
include "cpr.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "simpr.mm"
include "wn.mm"
include "csdm.mm"
include "c1o.mm"
include "wo.mm"
include "csn.mm"
include "cv.mm"
include "wss.mm"
include "toponss.mm"
include "ad2ant2rl.mm"
include "simprl.mm"
include "sseq0.mm"
include "syl2anc.mm"
include "velsn.mm"
include "sylibr.mm"
include "expr.mm"
include "ssrdv.mm"
include "ctop.mm"
include "topontop.mm"
include "0opn.mm"
include "syl.mm"
include "ad2antrr.mm"
include "snssd.mm"
include "eqssd.mm"
include "0ex.mm"
include "ensn1.mm"
include "syl6eqbr.mm"
include "olcd.mm"
include "sdom2en01.mm"
include "sdomnen.mm"
include "ex.mm"
include "necon2ad.mm"
include "mpd.mm"
include "necomd.mm"
include "wi.mm"
include "adantr.mm"
include "toponmax.mm"
include "en2eqpr.mm"
include "syl3anc.mm"
include "jca.mm"
include "cvv.mm"
include "a1i.mm"
include "simprr.mm"
include "pr2nelem.mm"
include "eqbrtrd.mm"
include "impbida.mm"

theorem en2top
  let cJ: class J
  let cX: class X
  let vx: setvar x


  assert |- ( J e. ( TopOn ` X ) -> ( J ~~ 2o <-> ( J = { (/) , X } /\ X =/= (/) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cJ
    c2o
    cen
    wbr
    #
    cJ
    c0
    cX
    cpr
    #
    wceq
    #
    cX
    c0
    wne
    #
    wa
    #
    @0
    @1
    wa
    #
    @3
    @4
    @6
    c0
    cX
    wne
    #
    @3
    @6
    cX
    c0
    @6
    @1
    @4
    @0
    @1
    simpr
    #
    @6
    @1
    cX
    c0
    @6
    cX
    c0
    wceq
    #
    @1
    wn
    #
    @6
    @9
    wa
    #
    cJ
    c2o
    csdm
    wbr
    #
    @10
    @11
    cJ
    c0
    wceq
    #
    cJ
    c1o
    cen
    wbr
    #
    wo
    @12
    @11
    @14
    @13
    @11
    cJ
    c0
    csn
    #
    c1o
    cen
    @11
    cJ
    @15
    @11
    vx
    cJ
    @15
    @6
    @9
    vx
    cv
    #
    cJ
    wcel
    #
    @16
    @15
    wcel
    #
    @6
    @9
    @17
    wa
    wa
    #
    @16
    c0
    wceq
    #
    @18
    @19
    @16
    cX
    wss
    #
    @9
    @20
    @0
    @17
    @21
    @1
    @9
    @16
    cJ
    cX
    toponss
    ad2ant2rl
    @6
    @9
    @17
    simprl
    @16
    cX
    sseq0
    syl2anc
    vx
    c0
    velsn
    sylibr
    expr
    ssrdv
    @11
    c0
    cJ
    @0
    c0
    cJ
    wcel
    #
    @1
    @9
    @0
    cJ
    ctop
    wcel
    @22
    cX
    cJ
    topontop
    cJ
    0opn
    syl
    #
    ad2antrr
    snssd
    eqssd
    c0
    0ex
    ensn1
    syl6eqbr
    olcd
    cJ
    sdom2en01
    sylibr
    cJ
    c2o
    sdomnen
    syl
    ex
    necon2ad
    mpd
    #
    necomd
    @6
    @1
    @22
    cX
    cJ
    wcel
    #
    @7
    @3
    wi
    @8
    @0
    @22
    @1
    @23
    adantr
    @0
    @25
    @1
    cX
    cJ
    toponmax
    #
    adantr
    c0
    cX
    cJ
    en2eqpr
    syl3anc
    mpd
    @24
    jca
    @0
    @5
    wa
    #
    cJ
    @2
    c2o
    cen
    @0
    @3
    @4
    simprl
    @27
    c0
    cvv
    wcel
    #
    @25
    @7
    @2
    c2o
    cen
    wbr
    @28
    @27
    0ex
    a1i
    @0
    @25
    @5
    @26
    adantr
    @27
    cX
    c0
    @0
    @3
    @4
    simprr
    necomd
    c0
    cX
    cvv
    cJ
    pr2nelem
    syl3anc
    eqbrtrd
    impbida
end
