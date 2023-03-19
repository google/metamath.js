include "cgru.mm"
include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "con0.mm"
include "wi.mm"
include "cv.mm"
include "wceq.mm"
include "breq1.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "wral.mm"
include "r19.21v.mm"
include "w3a.mm"
include "simpl1.mm"
include "cvv.mm"
include "wss.mm"
include "vex.mm"
include "onelss.mm"
include "imp.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "sylan.mm"
include "simplr.mm"
include "domtr.mm"
include "syl2anc.mm"
include "pm2.27.mm"
include "syl.mm"
include "ralimdva.mm"
include "dfss3.mm"
include "cen.mm"
include "wex.mm"
include "wb.mm"
include "domeng.mm"
include "3ad2ant3.mm"
include "biimpa.mm"
include "simpl2.mm"
include "gruss.mm"
include "3expia.mm"
include "3adant1.mm"
include "adantr.mm"
include "ensym.mm"
include "a1i.mm"
include "anim12d.mm"
include "ancomsd.mm"
include "eximdv.mm"
include "gruen.mm"
include "3com23.mm"
include "3exp.mm"
include "exlimdv.mm"
include "sylsyld.mm"
include "mpd.mm"
include "syl5bir.mm"
include "syld.mm"
include "ex.mm"
include "com23.mm"
include "3expib.mm"
include "a2d.mm"
include "syl5bi.mm"
include "tfis3.mm"
include "com3l.mm"
include "impr.mm"
include "3impia.mm"

theorem grudomon
  let cA: class A
  let cB: class B
  let cU: class U
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( U e. Univ /\ A e. On /\ ( B e. U /\ A ~<_ B ) ) -> A e. U )

  proof
    cU
    cgru
    wcel
    #
    cB
    cU
    wcel
    #
    cA
    cB
    cdom
    wbr
    #
    wa
    #
    cA
    con0
    wcel
    #
    cA
    cU
    wcel
    #
    @0
    @3
    @4
    @5
    @0
    @1
    @2
    @4
    @5
    wi
    @4
    @0
    @1
    wa
    #
    @2
    @5
    @6
    vx
    cv
    #
    cB
    cdom
    wbr
    #
    @7
    cU
    wcel
    #
    wi
    #
    wi
    #
    @6
    vy
    cv
    #
    cB
    cdom
    wbr
    #
    @12
    cU
    wcel
    #
    wi
    #
    wi
    #
    @6
    @2
    @5
    wi
    #
    wi
    vx
    vy
    cA
    @7
    @12
    wceq
    #
    @10
    @15
    @6
    @18
    @8
    @13
    @9
    @14
    @7
    @12
    cB
    cdom
    breq1
    @7
    @12
    cU
    eleq1
    imbi12d
    imbi2d
    @7
    cA
    wceq
    #
    @10
    @17
    @6
    @19
    @8
    @2
    @9
    @5
    @7
    cA
    cB
    cdom
    breq1
    @7
    cA
    cU
    eleq1
    imbi12d
    imbi2d
    @16
    vy
    @7
    wral
    @6
    @15
    vy
    @7
    wral
    #
    wi
    @7
    con0
    wcel
    #
    @11
    @6
    @15
    vy
    @7
    r19.21v
    @21
    @6
    @20
    @10
    @21
    @0
    @1
    @20
    @10
    wi
    @21
    @0
    @1
    w3a
    #
    @8
    @20
    @9
    @22
    @8
    @20
    @9
    wi
    @22
    @8
    wa
    #
    @20
    @14
    vy
    @7
    wral
    #
    @9
    @23
    @15
    @14
    vy
    @7
    @23
    @12
    @7
    wcel
    #
    wa
    #
    @13
    @15
    @14
    wi
    @26
    @12
    @7
    cdom
    wbr
    #
    @8
    @13
    @23
    @21
    @25
    @27
    @21
    @0
    @1
    @8
    simpl1
    @7
    cvv
    wcel
    @21
    @25
    wa
    @12
    @7
    wss
    #
    @27
    vx
    vex
    @21
    @25
    @28
    @7
    @12
    onelss
    imp
    @12
    @7
    cvv
    ssdomg
    mpsyl
    sylan
    @22
    @8
    @25
    simplr
    @12
    @7
    cB
    domtr
    syl2anc
    @13
    @14
    pm2.27
    syl
    ralimdva
    @24
    @7
    cU
    wss
    #
    @23
    @9
    vy
    @7
    cU
    dfss3
    @23
    @7
    @12
    cen
    wbr
    #
    @12
    cB
    wss
    #
    wa
    #
    vy
    wex
    #
    @29
    @9
    wi
    #
    @22
    @8
    @33
    @1
    @21
    @8
    @33
    wb
    @0
    vy
    @7
    cB
    cU
    domeng
    3ad2ant3
    biimpa
    @23
    @0
    @33
    @14
    @12
    @7
    cen
    wbr
    #
    wa
    #
    vy
    wex
    @34
    @21
    @0
    @1
    @8
    simpl2
    @23
    @32
    @36
    vy
    @23
    @31
    @30
    @36
    @23
    @31
    @14
    @30
    @35
    @22
    @31
    @14
    wi
    #
    @8
    @0
    @1
    @37
    @21
    @0
    @1
    @31
    @14
    cB
    @12
    cU
    gruss
    3expia
    3adant1
    adantr
    @30
    @35
    wi
    @23
    @7
    @12
    ensym
    a1i
    anim12d
    ancomsd
    eximdv
    @0
    @36
    @34
    vy
    @0
    @36
    @29
    @9
    @0
    @29
    @36
    @9
    @7
    @12
    cU
    gruen
    3com23
    3exp
    exlimdv
    sylsyld
    mpd
    syl5bir
    syld
    ex
    com23
    3expib
    a2d
    syl5bi
    tfis3
    com3l
    impr
    3impia
    3com23
end
