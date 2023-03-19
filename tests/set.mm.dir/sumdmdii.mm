include "cph.mm"
include "co.mm"
include "chj.mm"
include "wceq.mm"
include "cv.mm"
include "wss.mm"
include "cin.mm"
include "wi.mm"
include "cch.mm"
include "wral.mm"
include "cdmd.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "ineq2.mm"
include "adantr.mm"
include "wel.mm"
include "elin.mm"
include "cva.mm"
include "wrex.mm"
include "chseli.mm"
include "cmv.mm"
include "ssel2.mm"
include "csh.mm"
include "chsh.mm"
include "shsubcl.mm"
include "3exp.mm"
include "syl.mm"
include "syl7.mm"
include "exp4a.mm"
include "com23.mm"
include "imp41.mm"
include "adantlr.mm"
include "wb.mm"
include "chil.mm"
include "chel.mm"
include "cheli.mm"
include "w3a.mm"
include "hvsubadd.mm"
include "ax-hvcom.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "3adant1.mm"
include "bitrd.mm"
include "3com23.mm"
include "syl3an.mm"
include "3expa.mm"
include "eleq1.mm"
include "syl6bir.mm"
include "imp.mm"
include "mpbid.mm"
include "simpr.mm"
include "jca.mm"
include "exp31.mm"
include "reximdvai.mm"
include "r19.42v.mm"
include "syl6ib.mm"
include "reximdva.mm"
include "ancom.mm"
include "bitri.mm"
include "anbi1i.mm"
include "anass.mm"
include "rexbii2.mm"
include "syl6ibr.mm"
include "chshii.mm"
include "shincl.mm"
include "sylancl.mm"
include "ad2antrr.mm"
include "shsel.mm"
include "sylibrd.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "ssrdv.mm"
include "adantl.mm"
include "eqsstr3d.mm"
include "chincl.mm"
include "mpan2.mm"
include "chslej.mm"
include "ad2antrl.mm"
include "sstrd.mm"
include "exp32.mm"
include "ralrimiv.mm"
include "dmdbr2.mm"
include "mp2an.mm"
include "sylibr.mm"

theorem sumdmdii
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  assume sumdmdi.1: |- A e. CH
  assume sumdmdi.2: |- B e. CH


  assert |- ( ( A +H B ) = ( A vH B ) -> A MH* B )

  proof
    cA
    cB
    cph
    co
    #
    cA
    cB
    chj
    co
    #
    wceq
    #
    cB
    vx
    cv
    #
    wss
    #
    @3
    @1
    cin
    #
    @3
    cA
    cin
    #
    cB
    chj
    co
    #
    wss
    #
    wi
    #
    vx
    cch
    wral
    #
    cA
    cB
    cdmd
    wbr
    #
    @2
    @9
    vx
    cch
    @2
    @3
    cch
    wcel
    #
    @4
    @8
    @2
    @12
    @4
    wa
    #
    wa
    #
    @5
    @6
    cB
    cph
    co
    #
    @7
    @14
    @5
    @3
    @0
    cin
    #
    @15
    @2
    @16
    @5
    wceq
    @13
    @0
    @1
    @3
    ineq2
    adantr
    @13
    @16
    @15
    wss
    @2
    @13
    vy
    @16
    @15
    vy
    cv
    #
    @16
    wcel
    vy
    vx
    wel
    #
    @17
    @0
    wcel
    #
    wa
    @13
    @17
    @15
    wcel
    #
    @17
    @3
    @0
    elin
    @13
    @18
    @19
    @20
    @19
    @17
    vz
    cv
    #
    vw
    cv
    #
    cva
    co
    #
    wceq
    #
    vw
    cB
    wrex
    #
    vz
    cA
    wrex
    #
    @13
    @18
    wa
    #
    @20
    vz
    vw
    cA
    cB
    @17
    sumdmdi.1
    sumdmdi.2
    chseli
    @27
    @26
    @25
    vz
    @6
    wrex
    #
    @20
    @27
    @26
    vz
    vx
    wel
    #
    @25
    wa
    #
    vz
    cA
    wrex
    @28
    @27
    @25
    @30
    vz
    cA
    @27
    @21
    cA
    wcel
    #
    wa
    #
    @25
    @29
    @24
    wa
    #
    vw
    cB
    wrex
    @30
    @32
    @24
    @33
    vw
    cB
    @32
    @22
    cB
    wcel
    #
    @24
    @33
    @32
    @34
    wa
    #
    @24
    wa
    #
    @29
    @24
    @36
    @17
    @22
    cmv
    co
    #
    @3
    wcel
    #
    @29
    @35
    @38
    @24
    @27
    @34
    @38
    @31
    @12
    @4
    @18
    @34
    @38
    @12
    @18
    @4
    @34
    @38
    wi
    @12
    @18
    @4
    @34
    @38
    @4
    @34
    wa
    vw
    vx
    wel
    #
    @12
    @18
    @38
    cB
    @3
    @22
    ssel2
    @12
    @3
    csh
    wcel
    #
    @18
    @39
    @38
    wi
    wi
    @3
    chsh
    #
    @40
    @18
    @39
    @38
    @17
    @22
    @3
    shsubcl
    3exp
    syl
    syl7
    exp4a
    com23
    imp41
    adantlr
    adantr
    @35
    @24
    @38
    @29
    wb
    #
    @35
    @24
    @37
    @21
    wceq
    #
    @42
    @27
    @31
    @34
    @43
    @24
    wb
    #
    @27
    @17
    chil
    wcel
    #
    @31
    @21
    chil
    wcel
    #
    @34
    @22
    chil
    wcel
    #
    @44
    @12
    @18
    @45
    @4
    @17
    @3
    chel
    adantlr
    @21
    cA
    sumdmdi.1
    cheli
    @22
    cB
    sumdmdi.2
    cheli
    @45
    @47
    @46
    @44
    @45
    @47
    @46
    w3a
    @43
    @22
    @21
    cva
    co
    #
    @17
    wceq
    #
    @24
    @17
    @22
    @21
    hvsubadd
    @47
    @46
    @49
    @24
    wb
    @45
    @47
    @46
    wa
    #
    @49
    @23
    @17
    wceq
    @24
    @50
    @48
    @23
    @17
    @22
    @21
    ax-hvcom
    eqeq1d
    @23
    @17
    eqcom
    syl6bb
    3adant1
    bitrd
    3com23
    syl3an
    3expa
    @37
    @21
    @3
    eleq1
    syl6bir
    imp
    mpbid
    @35
    @24
    simpr
    jca
    exp31
    reximdvai
    @29
    @24
    vw
    cB
    r19.42v
    syl6ib
    reximdva
    @25
    @30
    vz
    @6
    cA
    @21
    @6
    wcel
    #
    @25
    wa
    @31
    @29
    wa
    #
    @25
    wa
    @31
    @30
    wa
    @51
    @52
    @25
    @51
    @29
    @31
    wa
    @52
    @21
    @3
    cA
    elin
    @29
    @31
    ancom
    bitri
    anbi1i
    @31
    @29
    @25
    anass
    bitri
    rexbii2
    syl6ibr
    @27
    @6
    csh
    wcel
    #
    cB
    csh
    wcel
    @20
    @28
    wb
    @12
    @53
    @4
    @18
    @12
    @40
    cA
    csh
    wcel
    @53
    @41
    cA
    sumdmdi.1
    chshii
    @3
    cA
    shincl
    sylancl
    ad2antrr
    cB
    sumdmdi.2
    chshii
    vz
    vw
    @6
    cB
    @17
    shsel
    sylancl
    sylibrd
    syl5bi
    expimpd
    syl5bi
    ssrdv
    adantl
    eqsstr3d
    @12
    @15
    @7
    wss
    #
    @2
    @4
    @12
    @6
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    @54
    @12
    cA
    cch
    wcel
    #
    @55
    sumdmdi.1
    @3
    cA
    chincl
    mpan2
    sumdmdi.2
    @6
    cB
    chslej
    sylancl
    ad2antrl
    sstrd
    exp32
    ralrimiv
    @57
    @56
    @11
    @10
    wb
    sumdmdi.1
    sumdmdi.2
    vx
    cA
    cB
    dmdbr2
    mp2an
    sylibr
end
