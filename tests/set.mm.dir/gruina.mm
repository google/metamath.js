include "cgru.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "ccf.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cpw.mm"
include "csdm.mm"
include "wbr.mm"
include "wral.mm"
include "cina.mm"
include "wex.mm"
include "wi.mm"
include "n0.mm"
include "con0.mm"
include "cin.mm"
include "wss.mm"
include "0ss.mm"
include "gruss.mm"
include "mp3an3.mm"
include "0elon.mm"
include "elin.mm"
include "sylanblrc.mm"
include "syl6eleqr.mm"
include "ne0i.mm"
include "syl.mm"
include "expcom.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "impcom.mm"
include "wn.mm"
include "word.mm"
include "cvv.mm"
include "wtr.mm"
include "cep.mm"
include "wwe.mm"
include "grutr.mm"
include "tron.mm"
include "trin.mm"
include "sylancl.mm"
include "inss2.mm"
include "epweon.mm"
include "wess.mm"
include "mp2.mm"
include "df-ord.mm"
include "inex1g.mm"
include "elon2.mm"
include "sylanbrc.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "eloni.mm"
include "ordirr.mm"
include "biimpri.mm"
include "mtod.mm"
include "ccrd.mm"
include "cuni.mm"
include "cab.mm"
include "cint.mm"
include "wlim.mm"
include "com.mm"
include "wrex.mm"
include "inss1.mm"
include "eqsstri.mm"
include "sseli.mm"
include "cdom.mm"
include "vpwex.mm"
include "canth2.mm"
include "cen.mm"
include "pwex.mm"
include "cardid.mm"
include "ensymi.mm"
include "grupw.mm"
include "syldan.mm"
include "endom.mm"
include "ax-mp.mm"
include "cardon.mm"
include "grudomon.mm"
include "mp3an2.mm"
include "mpanr2.mm"
include "onelss.mm"
include "sylc.mm"
include "ssdomg.mm"
include "endomtr.mm"
include "sylancr.mm"
include "sdomdomtr.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "inawinalem.mm"
include "winainflem.mm"
include "syl3anc.mm"
include "wb.mm"
include "vex.mm"
include "sdomtr.mm"
include "iscard.mm"
include "cardlim.mm"
include "sseq2.mm"
include "limeq.mm"
include "bibi12d.mm"
include "mpbii.mm"
include "mpbid.mm"
include "cflm.mm"
include "syl2anc.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "abssi.mm"
include "fvex.mm"
include "syl6eqelr.mm"
include "intex.mm"
include "sylibr.mm"
include "onint.mm"
include "eqeltrd.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "elab.mm"
include "sylib.mm"
include "w3a.mm"
include "simp2rr.mm"
include "simp1l.mm"
include "simp2rl.mm"
include "syl6ss.mm"
include "3ad2ant3.mm"
include "simp2l.mm"
include "syl6eqbr.mm"
include "gruen.mm"
include "syl112anc.mm"
include "gruuni.mm"
include "3exp.mm"
include "exlimdv.mm"
include "mpd.mm"
include "wo.mm"
include "cfon.mm"
include "cfle.mm"
include "onsseleq.mm"
include "mpan.mm"
include "ord.mm"
include "elina.mm"
include "syl3anbrc.mm"

theorem gruina
  let cA: class A
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume gruina.1: |- A = ( U i^i On )


  assert |- ( ( U e. Univ /\ U =/= (/) ) -> A e. Inacc )

  proof
    cU
    cgru
    wcel
    #
    cU
    c0
    wne
    #
    wa
    #
    cA
    c0
    wne
    #
    cA
    ccf
    cfv
    #
    cA
    wceq
    #
    vx
    cv
    #
    cpw
    #
    cA
    csdm
    wbr
    #
    vx
    cA
    wral
    #
    cA
    cina
    wcel
    @1
    @0
    @3
    @1
    @6
    cU
    wcel
    #
    vx
    wex
    @0
    @3
    wi
    #
    vx
    cU
    n0
    @10
    @11
    vx
    @0
    @10
    @3
    @0
    @10
    wa
    #
    c0
    cA
    wcel
    @3
    @12
    c0
    cU
    con0
    cin
    #
    cA
    @12
    c0
    cU
    wcel
    #
    c0
    con0
    wcel
    c0
    @13
    wcel
    @0
    @10
    c0
    @6
    wss
    @14
    @6
    0ss
    @6
    c0
    cU
    gruss
    mp3an3
    0elon
    c0
    cU
    con0
    elin
    sylanblrc
    gruina.1
    syl6eleqr
    cA
    c0
    ne0i
    syl
    expcom
    exlimiv
    sylbi
    impcom
    #
    @2
    cA
    con0
    wcel
    #
    @4
    cA
    wcel
    #
    wn
    @5
    @0
    @16
    @1
    @0
    cA
    @13
    con0
    gruina.1
    @0
    @13
    word
    #
    @13
    cvv
    wcel
    @13
    con0
    wcel
    @0
    @13
    wtr
    #
    @13
    cep
    wwe
    #
    @18
    @0
    cU
    wtr
    con0
    wtr
    @19
    cU
    grutr
    tron
    cU
    con0
    trin
    sylancl
    @13
    con0
    wss
    con0
    cep
    wwe
    @20
    cU
    con0
    inss2
    epweon
    @13
    con0
    cep
    wess
    mp2
    @13
    df-ord
    sylanblrc
    cU
    con0
    cgru
    inex1g
    @13
    elon2
    sylanbrc
    syl5eqel
    #
    adantr
    #
    @2
    @17
    cA
    cU
    wcel
    #
    @2
    @16
    @23
    wn
    @22
    @16
    @23
    cA
    cA
    wcel
    #
    @16
    cA
    word
    @24
    wn
    cA
    eloni
    cA
    ordirr
    syl
    @23
    @16
    @24
    @23
    @16
    wa
    #
    cA
    @13
    cA
    cA
    @13
    wcel
    @25
    cA
    cU
    con0
    elin
    biimpri
    gruina.1
    syl6eleqr
    expcom
    mtod
    syl
    @2
    @4
    vy
    cv
    #
    ccrd
    cfv
    #
    wceq
    #
    @26
    cA
    wss
    #
    cA
    @26
    cuni
    #
    wceq
    #
    wa
    #
    wa
    #
    vy
    wex
    #
    @17
    @23
    wi
    #
    @2
    @4
    @6
    @27
    wceq
    #
    @32
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    wcel
    @34
    @2
    @4
    @39
    cint
    #
    @39
    @2
    @16
    cA
    wlim
    #
    @4
    @40
    wceq
    @22
    @2
    com
    cA
    wss
    #
    @41
    @2
    @3
    @16
    @6
    @26
    csdm
    wbr
    vy
    cA
    wrex
    vx
    cA
    wral
    #
    @42
    @15
    @22
    @0
    @43
    @1
    @0
    @16
    @9
    @43
    @21
    @0
    @8
    vx
    cA
    @6
    cA
    wcel
    #
    @0
    @10
    @8
    cA
    cU
    @6
    cA
    @13
    cU
    gruina.1
    cU
    con0
    inss1
    eqsstri
    #
    sseli
    @12
    @7
    @7
    cpw
    #
    csdm
    wbr
    @46
    cA
    cdom
    wbr
    #
    @8
    @7
    vx
    vpwex
    #
    canth2
    @12
    @46
    @46
    ccrd
    cfv
    #
    cen
    wbr
    @49
    cA
    cdom
    wbr
    #
    @47
    @49
    @46
    @46
    @7
    @48
    pwex
    cardid
    #
    ensymi
    @12
    @16
    @49
    cA
    wss
    #
    @50
    @0
    @16
    @10
    @21
    adantr
    @0
    @10
    @46
    cU
    wcel
    #
    @52
    @0
    @10
    @7
    cU
    wcel
    @53
    @6
    cU
    grupw
    @7
    cU
    grupw
    syldan
    @0
    @53
    wa
    #
    @16
    @49
    cA
    wcel
    #
    @52
    @0
    @16
    @53
    @21
    adantr
    @54
    @49
    cU
    wcel
    #
    @49
    con0
    wcel
    #
    @55
    @0
    @53
    @49
    @46
    cdom
    wbr
    #
    @56
    @49
    @46
    cen
    wbr
    @58
    @51
    @49
    @46
    endom
    ax-mp
    @0
    @57
    @53
    @58
    wa
    @56
    @46
    cardon
    #
    @49
    @46
    cU
    grudomon
    mp3an2
    mpanr2
    @59
    @56
    @57
    wa
    #
    @49
    @13
    cA
    @49
    @13
    wcel
    @60
    @49
    cU
    con0
    elin
    biimpri
    gruina.1
    syl6eleqr
    sylancl
    cA
    @49
    onelss
    sylc
    syldan
    @49
    cA
    con0
    ssdomg
    sylc
    @46
    @49
    cA
    endomtr
    sylancr
    @7
    @46
    cA
    sdomdomtr
    sylancr
    sylan2
    #
    ralrimiva
    #
    vx
    vy
    cA
    inawinalem
    sylc
    adantr
    vx
    vy
    cA
    winainflem
    syl3anc
    @0
    @42
    @41
    wb
    #
    @1
    @0
    cA
    ccrd
    cfv
    #
    cA
    wceq
    #
    @63
    @0
    @16
    @6
    cA
    csdm
    wbr
    #
    vx
    cA
    wral
    @65
    @21
    @0
    @66
    vx
    cA
    @0
    @44
    wa
    @6
    @7
    csdm
    wbr
    @8
    @66
    @6
    vx
    vex
    canth2
    @61
    @6
    @7
    cA
    sdomtr
    sylancr
    ralrimiva
    vx
    cA
    iscard
    sylanbrc
    @65
    com
    @64
    wss
    #
    @64
    wlim
    #
    wb
    @63
    cA
    cardlim
    @65
    @67
    @42
    @68
    @41
    @64
    cA
    com
    sseq2
    @64
    cA
    limeq
    bibi12d
    mpbii
    syl
    adantr
    mpbid
    vx
    vy
    cA
    con0
    cflm
    syl2anc
    #
    @2
    @39
    con0
    wss
    @39
    c0
    wne
    #
    @40
    @39
    wcel
    @38
    vx
    con0
    @37
    @6
    con0
    wcel
    #
    vy
    @36
    @71
    @32
    @36
    @71
    @27
    con0
    wcel
    @26
    cardon
    @6
    @27
    con0
    eleq1
    mpbiri
    adantr
    exlimiv
    abssi
    @2
    @40
    cvv
    wcel
    @70
    @2
    @40
    @4
    cvv
    @69
    cA
    ccf
    fvex
    #
    syl6eqelr
    @39
    intex
    sylibr
    @39
    onint
    sylancr
    eqeltrd
    @38
    @34
    vx
    @4
    @72
    @6
    @4
    wceq
    #
    @37
    @33
    vy
    @73
    @36
    @28
    @32
    @6
    @4
    @27
    eqeq1
    anbi1d
    exbidv
    elab
    sylib
    @2
    @33
    @35
    vy
    @2
    @33
    @17
    @23
    @2
    @33
    @17
    w3a
    #
    cA
    @30
    cU
    @29
    @31
    @28
    @2
    @17
    simp2rr
    @74
    @0
    @26
    cU
    wcel
    #
    @30
    cU
    wcel
    @0
    @1
    @33
    @17
    simp1l
    #
    @74
    @0
    @26
    cU
    wss
    @4
    cU
    wcel
    #
    @4
    @26
    cen
    wbr
    @75
    @76
    @74
    @26
    cA
    cU
    @29
    @31
    @28
    @2
    @17
    simp2rl
    @45
    syl6ss
    @17
    @2
    @77
    @33
    cA
    cU
    @4
    @45
    sseli
    3ad2ant3
    @74
    @4
    @27
    @26
    cen
    @2
    @28
    @32
    @17
    simp2l
    @26
    vy
    vex
    cardid
    syl6eqbr
    @26
    @4
    cU
    gruen
    syl112anc
    @26
    cU
    gruuni
    syl2anc
    eqeltrd
    3exp
    exlimdv
    mpd
    mtod
    @16
    @17
    @5
    @4
    con0
    wcel
    #
    @16
    @17
    @5
    wo
    #
    cA
    cfon
    @78
    @16
    wa
    @4
    cA
    wss
    @79
    cA
    cfle
    @4
    cA
    onsseleq
    mpbii
    mpan
    ord
    sylc
    @0
    @9
    @1
    @62
    adantr
    vx
    cA
    elina
    syl3anbrc
end
