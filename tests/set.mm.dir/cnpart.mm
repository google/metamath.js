include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "crp.mm"
include "wnel.mm"
include "cneg.mm"
include "wn.mm"
include "wb.mm"
include "wceq.mm"
include "df-nel.mm"
include "simpr.mm"
include "0le0.mm"
include "syl6eqbr.mm"
include "biantrurd.mm"
include "syl5bbr.mm"
include "con1bid.mm"
include "cr.mm"
include "cim.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "reim0b.mm"
include "syl.mm"
include "imre.mm"
include "cdiv.mm"
include "c1.mm"
include "ine0.mm"
include "divrec2.mm"
include "mp3an23.mm"
include "irec.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "divcan3.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "biimpar.mm"
include "adantlr.mm"
include "mulne0.mm"
include "mpanl12.mm"
include "adantr.mm"
include "rpneg.mm"
include "syl2anc.mm"
include "con2bid.mm"
include "syl6bbr.mm"
include "syl5breqr.mm"
include "3bitrrd.mm"
include "necon3bbid.mm"
include "rpre.mm"
include "nsyl.mm"
include "sylibr.mm"
include "biantrud.mm"
include "0re.mm"
include "recl.mm"
include "clt.mm"
include "ltlen.mm"
include "ltnle.mm"
include "bitr3d.mm"
include "sylancr.mm"
include "ad2antrr.mm"
include "renegcl.mm"
include "negnegd.mm"
include "eleq1d.mm"
include "syl5ib.mm"
include "mtod.mm"
include "notbid.mm"
include "pm2.61dane.mm"
include "reneg.mm"
include "breq2d.mm"
include "le0neg1d.mm"
include "bitr4d.mm"
include "mulneg2.mm"
include "neleq1.mm"
include "anbi12d.mm"

theorem cnpart
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( ( 0 <_ ( Re ` A ) /\ ( _i x. A ) e/ RR+ ) <-> -. ( 0 <_ ( Re ` -u A ) /\ ( _i x. -u A ) e/ RR+ ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cc0
    cA
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    cA
    cmul
    co
    #
    crp
    wnel
    #
    wa
    #
    @3
    cc0
    cle
    wbr
    #
    @5
    cneg
    #
    crp
    wnel
    #
    wa
    #
    wn
    #
    cc0
    cA
    cneg
    #
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    @13
    cmul
    co
    #
    crp
    wnel
    #
    wa
    #
    wn
    #
    @2
    @7
    @12
    wb
    @3
    cc0
    @2
    @3
    cc0
    wceq
    #
    wa
    #
    @12
    @9
    crp
    wcel
    #
    @6
    @7
    @21
    @22
    @11
    @22
    wn
    #
    @10
    @21
    @11
    @9
    crp
    df-nel
    #
    @21
    @8
    @10
    @21
    @3
    cc0
    cc0
    cle
    @2
    @20
    simpr
    #
    0le0
    syl6eqbr
    biantrurd
    syl5bbr
    con1bid
    @21
    @22
    @5
    crp
    wcel
    #
    wn
    #
    @6
    @21
    @26
    @22
    @21
    @5
    cr
    wcel
    #
    @5
    cc0
    wne
    #
    @26
    @23
    wb
    @0
    @20
    @28
    @1
    @0
    @28
    @20
    @0
    @28
    @5
    cim
    cfv
    #
    cc0
    wceq
    #
    @20
    @0
    @5
    cc
    wcel
    #
    @28
    @31
    wb
    ci
    cc
    wcel
    #
    @0
    @32
    ax-icn
    ci
    cA
    mulcl
    mpan
    #
    @5
    reim0b
    syl
    @0
    @30
    @3
    cc0
    @0
    @30
    ci
    cneg
    #
    @5
    cmul
    co
    #
    cre
    cfv
    #
    @3
    @0
    @32
    @30
    @37
    wceq
    @34
    @5
    imre
    syl
    @0
    @36
    cA
    cre
    @0
    @5
    ci
    cdiv
    co
    #
    @36
    cA
    @0
    @38
    c1
    ci
    cdiv
    co
    #
    @5
    cmul
    co
    #
    @36
    @0
    @32
    @38
    @40
    wceq
    #
    @34
    @32
    @33
    ci
    cc0
    wne
    #
    @41
    ax-icn
    ine0
    @5
    ci
    divrec2
    mp3an23
    syl
    @39
    @35
    @5
    cmul
    irec
    oveq1i
    syl6eq
    @0
    @33
    @42
    @38
    cA
    wceq
    ax-icn
    ine0
    cA
    ci
    divcan3
    mp3an23
    eqtr3d
    fveq2d
    eqtrd
    eqeq1d
    bitrd
    #
    biimpar
    adantlr
    @2
    @29
    @20
    @33
    @42
    @2
    @29
    ax-icn
    ine0
    ci
    cA
    mulne0
    mpanl12
    adantr
    @5
    rpneg
    syl2anc
    con2bid
    @5
    crp
    df-nel
    #
    syl6bbr
    @21
    @4
    @6
    @21
    cc0
    cc0
    @3
    cle
    0le0
    @25
    syl5breqr
    biantrurd
    3bitrrd
    @2
    @3
    cc0
    wne
    #
    wa
    #
    @7
    @8
    wn
    #
    @12
    @46
    @4
    @7
    @47
    @46
    @6
    @4
    @46
    @27
    @6
    @46
    @28
    @26
    @2
    @28
    wn
    @45
    @2
    @28
    @3
    cc0
    @0
    @28
    @20
    wb
    @1
    @43
    adantr
    necon3bbid
    biimpar
    #
    @5
    rpre
    nsyl
    @44
    sylibr
    biantrud
    @46
    @4
    @4
    @45
    wa
    #
    @47
    @46
    @45
    @4
    @2
    @45
    simpr
    biantrud
    @0
    @49
    @47
    wb
    #
    @1
    @45
    @0
    cc0
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @50
    0re
    cA
    recl
    #
    @51
    @52
    wa
    cc0
    @3
    clt
    wbr
    @49
    @47
    cc0
    @3
    ltlen
    cc0
    @3
    ltnle
    bitr3d
    sylancr
    ad2antrr
    bitrd
    bitr3d
    @46
    @8
    @11
    @46
    @10
    @8
    @46
    @23
    @10
    @46
    @9
    cr
    wcel
    #
    @22
    @46
    @54
    @28
    @48
    @54
    @9
    cneg
    #
    cr
    wcel
    #
    @46
    @28
    @9
    renegcl
    @0
    @56
    @28
    wb
    @1
    @45
    @0
    @55
    @5
    cr
    @0
    @5
    @34
    negnegd
    eleq1d
    ad2antrr
    syl5ib
    mtod
    @9
    rpre
    nsyl
    @24
    sylibr
    biantrud
    notbid
    bitrd
    pm2.61dane
    @0
    @19
    @12
    wb
    @1
    @0
    @18
    @11
    @0
    @15
    @8
    @17
    @10
    @0
    @15
    cc0
    @3
    cneg
    #
    cle
    wbr
    @8
    @0
    @14
    @57
    cc0
    cle
    cA
    reneg
    breq2d
    @0
    @3
    @53
    le0neg1d
    bitr4d
    @0
    @16
    @9
    wceq
    #
    @17
    @10
    wb
    @33
    @0
    @58
    ax-icn
    ci
    cA
    mulneg2
    mpan
    @16
    @9
    crp
    neleq1
    syl
    anbi12d
    notbid
    adantr
    bitr4d
end
