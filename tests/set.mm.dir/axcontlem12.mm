include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wss.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "wi.mm"
include "c0.mm"
include "wceq.mm"
include "rzal.mm"
include "ralrimivw.mm"
include "breq1.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "expcom.mm"
include "syl.mm"
include "adantld.mm"
include "simprrl.mm"
include "simprrr.mm"
include "simprll.mm"
include "simpl.mm"
include "3jca.mm"
include "simprlr.mm"
include "axcontlem11.mm"
include "syl12anc.mm"
include "ex.mm"
include "pm2.61ine.mm"
include "rexlimiva.mm"
include "wn.mm"
include "df-ne.mm"
include "con2bii.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"
include "simpr3.mm"
include "wb.mm"
include "eqeq2.mm"
include "rspccva.mm"
include "opeq1.mm"
include "breq2d.mm"
include "bitr4d.mm"
include "ralbidv.mm"
include "ralbidva.mm"
include "biimpa.mm"
include "sylan2.mm"
include "ancoms.mm"
include "expl.mm"
include "sylbir.mm"
include "pm2.61i.mm"

theorem axcontlem12
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cN: class N
  let cZ: class Z
  let vb: setvar b
  let vu: setvar u

  disjoint A b
  disjoint A x
  disjoint b x
  disjoint B b
  disjoint B x
  disjoint B y
  disjoint b y
  disjoint x y
  disjoint N b
  disjoint N x
  disjoint N y
  disjoint Z b
  disjoint Z x
  disjoint Z y
  disjoint A u
  disjoint b u
  disjoint u x
  disjoint B u
  disjoint u y
  disjoint N u
  disjoint Z u
  assert |- ( ( ( N e. NN /\ ( A C_ ( EE ` N ) /\ B C_ ( EE ` N ) /\ A. x e. A A. y e. B x Btwn <. Z , y >. ) ) /\ Z e. ( EE ` N ) ) -> E. b e. ( EE ` N ) A. x e. A A. y e. B b Btwn <. x , y >. )

  proof
    cZ
    vu
    cv
    #
    wne
    #
    vu
    cA
    wrex
    #
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wss
    #
    cB
    @4
    wss
    #
    vx
    cv
    #
    cZ
    vy
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    w3a
    wa
    #
    cZ
    @4
    wcel
    #
    wa
    #
    vb
    cv
    #
    @7
    @8
    cop
    #
    cbtwn
    wbr
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    vb
    @4
    wrex
    #
    wi
    #
    @1
    @21
    vu
    cA
    @0
    cA
    wcel
    #
    @1
    wa
    #
    @15
    @20
    @23
    @15
    wa
    #
    @20
    wi
    cB
    c0
    cB
    c0
    wceq
    #
    @15
    @20
    @23
    @25
    @14
    @20
    @13
    @25
    cZ
    @17
    cbtwn
    wbr
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    @14
    @20
    wi
    @25
    @27
    vx
    cA
    @26
    vy
    cB
    rzal
    ralrimivw
    @14
    @28
    @20
    @19
    @28
    vb
    cZ
    @4
    @16
    cZ
    wceq
    @18
    @26
    vx
    vy
    cA
    cB
    @16
    cZ
    @17
    cbtwn
    breq1
    2ralbidv
    rspcev
    #
    expcom
    syl
    adantld
    adantld
    cB
    c0
    wne
    #
    @24
    @20
    @30
    @24
    wa
    #
    @13
    @14
    @22
    @30
    w3a
    @1
    @20
    @30
    @23
    @13
    @14
    simprrl
    @31
    @14
    @22
    @30
    @30
    @23
    @13
    @14
    simprrr
    @30
    @22
    @1
    @15
    simprll
    @30
    @24
    simpl
    3jca
    @30
    @22
    @1
    @15
    simprlr
    vx
    vy
    cA
    cB
    @0
    cN
    cZ
    vb
    axcontlem11
    syl12anc
    ex
    pm2.61ine
    ex
    rexlimiva
    @2
    wn
    #
    cZ
    @0
    wceq
    #
    vu
    cA
    wral
    #
    @21
    @34
    @1
    wn
    #
    vu
    cA
    wral
    @32
    @33
    @35
    vu
    cA
    @1
    @33
    cZ
    @0
    df-ne
    con2bii
    ralbii
    @1
    vu
    cA
    ralnex
    bitri
    @34
    @13
    @14
    @20
    @14
    @34
    @13
    wa
    #
    @20
    @36
    @14
    @28
    @20
    @13
    @34
    @12
    @28
    @3
    @5
    @6
    @12
    simpr3
    @34
    @12
    @28
    @34
    @11
    @27
    vx
    cA
    @34
    @7
    cA
    wcel
    wa
    cZ
    @7
    wceq
    #
    @11
    @27
    wb
    @33
    @37
    vu
    @7
    cA
    @0
    @7
    cZ
    eqeq2
    rspccva
    @37
    @10
    @26
    vy
    cB
    @37
    @10
    @7
    @17
    cbtwn
    wbr
    @26
    @37
    @9
    @17
    @7
    cbtwn
    cZ
    @7
    @8
    opeq1
    breq2d
    cZ
    @7
    @17
    cbtwn
    breq1
    bitr4d
    ralbidv
    syl
    ralbidva
    biimpa
    sylan2
    @29
    sylan2
    ancoms
    expl
    sylbir
    pm2.61i
end
