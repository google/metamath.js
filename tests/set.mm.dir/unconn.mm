include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "crest.mm"
include "co.mm"
include "cconn.mm"
include "cun.mm"
include "wi.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "w3a.mm"
include "cpr.mm"
include "ciun.mm"
include "cuni.mm"
include "uniiun.mm"
include "cvv.mm"
include "wceq.mm"
include "simpl1.mm"
include "toponmax.mm"
include "syl.mm"
include "simpl2l.mm"
include "ssexd.mm"
include "simpl2r.mm"
include "uniprg.mm"
include "syl2anc.mm"
include "syl5eqr.mm"
include "oveq2d.mm"
include "wo.mm"
include "vex.mm"
include "elpr.mm"
include "simpl2.mm"
include "sseq1.mm"
include "biimprd.mm"
include "jaoa.mm"
include "mpan9.mm"
include "sylan2b.mm"
include "simpl3.mm"
include "elin.mm"
include "sylib.mm"
include "eleq2.mm"
include "simpr.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "iunconn.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "3expia.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "3impia.mm"

theorem unconn
  let cA: class A
  let cB: class B
  let cJ: class J
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cT: class T


  assert |- ( ( J e. ( TopOn ` X ) /\ ( A C_ X /\ B C_ X ) /\ ( A i^i B ) =/= (/) ) -> ( ( ( J |`t A ) e. Conn /\ ( J |`t B ) e. Conn ) -> ( J |`t ( A u. B ) ) e. Conn ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cA
    cX
    wss
    #
    cB
    cX
    wss
    #
    wa
    #
    cA
    cB
    cin
    #
    c0
    wne
    #
    cJ
    cA
    crest
    co
    #
    cconn
    wcel
    #
    cJ
    cB
    crest
    co
    #
    cconn
    wcel
    #
    wa
    #
    cJ
    cA
    cB
    cun
    #
    crest
    co
    #
    cconn
    wcel
    #
    wi
    #
    @5
    vx
    cv
    #
    @4
    wcel
    #
    vx
    wex
    @0
    @3
    wa
    #
    @14
    vx
    @4
    n0
    @17
    @16
    @14
    vx
    @0
    @3
    @16
    @14
    @0
    @3
    @16
    w3a
    #
    @10
    @13
    @18
    @10
    wa
    #
    cJ
    vk
    cA
    cB
    cpr
    #
    vk
    cv
    #
    ciun
    #
    crest
    co
    @12
    cconn
    @19
    @22
    @11
    cJ
    crest
    @19
    @22
    @20
    cuni
    #
    @11
    vk
    @20
    uniiun
    @19
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    @23
    @11
    wceq
    @19
    cA
    cX
    cJ
    @19
    @0
    cX
    cJ
    wcel
    @0
    @3
    @16
    @10
    simpl1
    #
    cX
    cJ
    toponmax
    syl
    #
    @1
    @2
    @0
    @16
    @10
    simpl2l
    ssexd
    @19
    cB
    cX
    cJ
    @25
    @1
    @2
    @0
    @16
    @10
    simpl2r
    ssexd
    cA
    cB
    cvv
    cvv
    uniprg
    syl2anc
    syl5eqr
    oveq2d
    @19
    @20
    @21
    @15
    vk
    cJ
    cX
    @24
    @21
    @20
    wcel
    #
    @19
    @21
    cA
    wceq
    #
    @21
    cB
    wceq
    #
    wo
    #
    @21
    cX
    wss
    #
    @21
    cA
    cB
    vk
    vex
    elpr
    #
    @19
    @3
    @29
    @30
    @0
    @3
    @16
    @10
    simpl2
    @27
    @1
    @30
    @28
    @2
    @27
    @30
    @1
    @21
    cA
    cX
    sseq1
    biimprd
    @28
    @30
    @2
    @21
    cB
    cX
    sseq1
    biimprd
    jaoa
    mpan9
    sylan2b
    @26
    @19
    @29
    @15
    @21
    wcel
    #
    @31
    @19
    @15
    cA
    wcel
    #
    @15
    cB
    wcel
    #
    wa
    #
    @29
    @32
    @19
    @16
    @35
    @0
    @3
    @16
    @10
    simpl3
    @15
    cA
    cB
    elin
    sylib
    @27
    @33
    @32
    @28
    @34
    @27
    @32
    @33
    @21
    cA
    @15
    eleq2
    biimprd
    @28
    @32
    @34
    @21
    cB
    @15
    eleq2
    biimprd
    jaoa
    mpan9
    sylan2b
    @26
    @19
    @29
    cJ
    @21
    crest
    co
    #
    cconn
    wcel
    #
    @31
    @19
    @10
    @29
    @37
    @18
    @10
    simpr
    @27
    @7
    @37
    @28
    @9
    @27
    @37
    @7
    @27
    @36
    @6
    cconn
    @21
    cA
    cJ
    crest
    oveq2
    eleq1d
    biimprd
    @28
    @37
    @9
    @28
    @36
    @8
    cconn
    @21
    cB
    cJ
    crest
    oveq2
    eleq1d
    biimprd
    jaoa
    mpan9
    sylan2b
    iunconn
    eqeltrrd
    ex
    3expia
    exlimdv
    syl5bi
    3impia
end
