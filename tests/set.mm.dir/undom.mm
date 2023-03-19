include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "cen.mm"
include "wss.mm"
include "wex.mm"
include "cdif.mm"
include "cun.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "domeng.mm"
include "syl.mm"
include "ibi.mm"
include "brrelexi.mm"
include "difss.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "domtr.mm"
include "mpancom.mm"
include "anim12i.mm"
include "adantr.mm"
include "eeanv.mm"
include "simprll.mm"
include "simprrl.mm"
include "disjdif.mm"
include "a1i.mm"
include "ss2in.mm"
include "ad2ant2l.mm"
include "adantl.mm"
include "simplr.mm"
include "sseq0.mm"
include "syl2anc.mm"
include "undif2.mm"
include "unen.mm"
include "syl5eqbrr.mm"
include "syl22anc.mm"
include "ad3antrrr.mm"
include "ad3antlr.mm"
include "unexg.mm"
include "unss12.mm"
include "sylc.mm"
include "endomtr.mm"
include "ex.mm"
include "exlimdvv.mm"
include "syl5bir.mm"
include "mpd.mm"

theorem undom
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( A ~<_ B /\ C ~<_ D ) /\ ( B i^i D ) = (/) ) -> ( A u. C ) ~<_ ( B u. D ) )

  proof
    cA
    cB
    cdom
    wbr
    #
    cC
    cD
    cdom
    wbr
    #
    wa
    #
    cB
    cD
    cin
    #
    c0
    wceq
    #
    wa
    #
    cA
    vx
    cv
    #
    cen
    wbr
    #
    @6
    cB
    wss
    #
    wa
    #
    vx
    wex
    #
    cC
    cA
    cdif
    #
    vy
    cv
    #
    cen
    wbr
    #
    @12
    cD
    wss
    #
    wa
    #
    vy
    wex
    #
    wa
    #
    cA
    cC
    cun
    #
    cB
    cD
    cun
    #
    cdom
    wbr
    #
    @2
    @17
    @4
    @0
    @10
    @1
    @16
    @0
    @10
    @0
    cB
    cvv
    wcel
    #
    @0
    @10
    wb
    cA
    cB
    cdom
    reldom
    brrelex2i
    #
    vx
    cA
    cB
    cvv
    domeng
    syl
    ibi
    @1
    @11
    cD
    cdom
    wbr
    #
    @16
    @11
    cC
    cdom
    wbr
    #
    @1
    @23
    @1
    cC
    cvv
    wcel
    @11
    cC
    wss
    @24
    cC
    cD
    cdom
    reldom
    brrelexi
    cC
    cA
    difss
    @11
    cC
    cvv
    ssdomg
    mpisyl
    @11
    cC
    cD
    domtr
    mpancom
    @23
    @16
    @23
    cD
    cvv
    wcel
    #
    @23
    @16
    wb
    @11
    cD
    cdom
    reldom
    brrelex2i
    vy
    @11
    cD
    cvv
    domeng
    syl
    ibi
    syl
    anim12i
    adantr
    @17
    @9
    @15
    wa
    #
    vy
    wex
    vx
    wex
    @5
    @20
    @9
    @15
    vx
    vy
    eeanv
    @5
    @26
    @20
    vx
    vy
    @5
    @26
    @20
    @5
    @26
    wa
    #
    @18
    @6
    @12
    cun
    #
    cen
    wbr
    #
    @28
    @19
    cdom
    wbr
    #
    @20
    @27
    @7
    @13
    cA
    @11
    cin
    c0
    wceq
    #
    @6
    @12
    cin
    #
    c0
    wceq
    #
    @29
    @5
    @7
    @8
    @15
    simprll
    @5
    @9
    @13
    @14
    simprrl
    @31
    @27
    cA
    cC
    disjdif
    a1i
    @27
    @32
    @3
    wss
    #
    @4
    @33
    @26
    @34
    @5
    @8
    @14
    @34
    @7
    @13
    @6
    cB
    @12
    cD
    ss2in
    ad2ant2l
    adantl
    @2
    @4
    @26
    simplr
    @32
    @3
    sseq0
    syl2anc
    @7
    @13
    wa
    @31
    @33
    wa
    wa
    @18
    cA
    @11
    cun
    @28
    cen
    cA
    cC
    undif2
    cA
    @6
    @11
    @12
    unen
    syl5eqbrr
    syl22anc
    @27
    @19
    cvv
    wcel
    #
    @28
    @19
    wss
    #
    @30
    @27
    @21
    @25
    @35
    @0
    @21
    @1
    @4
    @26
    @22
    ad3antrrr
    @1
    @25
    @0
    @4
    @26
    cC
    cD
    cdom
    reldom
    brrelex2i
    ad3antlr
    cB
    cD
    cvv
    cvv
    unexg
    syl2anc
    @26
    @36
    @5
    @8
    @14
    @36
    @7
    @13
    @6
    cB
    @12
    cD
    unss12
    ad2ant2l
    adantl
    @28
    @19
    cvv
    ssdomg
    sylc
    @18
    @28
    @19
    endomtr
    syl2anc
    ex
    exlimdvv
    syl5bir
    mpd
end
