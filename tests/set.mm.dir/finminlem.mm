include "cfn.mm"
include "wrex.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "com.mm"
include "crab.mm"
include "c0.mm"
include "wne.mm"
include "cin.mm"
include "wceq.mm"
include "wss.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "nfe1.mm"
include "nfcv.mm"
include "nfrab.mm"
include "nfne.mm"
include "wcel.mm"
include "isfi.mm"
include "w3a.mm"
include "19.8a.mm"
include "anim2i.mm"
include "3impb.mm"
include "breq2.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "elrab.mm"
include "sylibr.mm"
include "ne0i.mm"
include "syl.mm"
include "3exp.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "rexlimi.mm"
include "con0.mm"
include "cep.mm"
include "wwe.mm"
include "epweon.mm"
include "ssrab2.mm"
include "omsson.mm"
include "sstri.mm"
include "wefrc.mm"
include "mp3an12.mm"
include "nfv.mm"
include "nfin.mm"
include "nfeq1.mm"
include "nfan.mm"
include "simprr.mm"
include "wpss.mm"
include "wo.mm"
include "sspss.mm"
include "wn.mm"
include "rspe.mm"
include "pssss.mm"
include "ssfi.mm"
include "sylan2.mm"
include "ex.mm"
include "sylbir.mm"
include "adantrr.mm"
include "simprll.mm"
include "simprlr.mm"
include "simplrr.mm"
include "vex.mm"
include "breq1.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl2anc.mm"
include "csdm.mm"
include "adantr.mm"
include "php3.mm"
include "cdom.mm"
include "cvv.mm"
include "ssdomg.mm"
include "ax-mp.mm"
include "endomtr.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "ensym.mm"
include "domentr.mm"
include "expcom.mm"
include "ad2antll.mm"
include "syld.mm"
include "syl5.mm"
include "domnsym.mm"
include "con2i.mm"
include "nsyli.mm"
include "impr.mm"
include "word.mm"
include "wb.mm"
include "nnord.mm"
include "ad2antrl.mm"
include "ordtri1.mm"
include "con2bid.mm"
include "mpbird.mm"
include "jca31.mm"
include "elin.mm"
include "anbi1i.mm"
include "bitri.mm"
include "exp44.mm"
include "rexlimdv.mm"
include "syl5bi.mm"
include "com23.mm"
include "mpdd.mm"
include "necon2bd.mm"
include "imp31.mm"
include "pm2.21d.mm"
include "equcomi.mm"
include "a1i.mm"
include "jaod.mm"
include "expr.mm"
include "impd.mm"
include "alrimiv.mm"
include "jca.mm"
include "eximd.mm"
include "impancom.mm"
include "3syl.mm"

theorem finminlem
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  assume finminlem.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint ph y
  disjoint ps x
  disjoint x y
  disjoint k m
  disjoint k n
  disjoint k y
  disjoint k ph
  disjoint m n
  disjoint m y
  disjoint m ph
  disjoint n y
  disjoint n ph
  disjoint k x
  disjoint k ps
  disjoint m x
  disjoint m ps
  disjoint n x
  disjoint n ps
  assert |- ( E. x e. Fin ph -> E. x ( ph /\ A. y ( ( y C_ x /\ ps ) -> x = y ) ) )

  proof
    wph
    vx
    cfn
    wrex
    vx
    cv
    #
    vn
    cv
    #
    cen
    wbr
    #
    wph
    wa
    #
    vx
    wex
    #
    vn
    com
    crab
    #
    c0
    wne
    #
    @5
    vm
    cv
    #
    cin
    #
    c0
    wceq
    #
    vm
    @5
    wrex
    #
    wph
    vy
    cv
    #
    @0
    wss
    #
    wps
    wa
    vx
    vy
    weq
    #
    wi
    #
    vy
    wal
    #
    wa
    #
    vx
    wex
    #
    wph
    @6
    vx
    cfn
    vx
    @5
    c0
    @4
    vx
    vn
    com
    @3
    vx
    nfe1
    vx
    com
    nfcv
    nfrab
    #
    vx
    c0
    nfcv
    nfne
    @0
    cfn
    wcel
    #
    @0
    @7
    cen
    wbr
    #
    vm
    com
    wrex
    #
    wph
    @6
    wi
    #
    vm
    @0
    isfi
    #
    @20
    @22
    vm
    com
    @7
    com
    wcel
    #
    @20
    wph
    @6
    @24
    @20
    wph
    w3a
    #
    @7
    @5
    wcel
    #
    @6
    @25
    @24
    @20
    wph
    wa
    #
    vx
    wex
    #
    wa
    #
    @26
    @24
    @20
    wph
    @29
    @27
    @28
    @24
    @27
    vx
    19.8a
    anim2i
    3impb
    @4
    @28
    vn
    @7
    com
    vn
    vm
    weq
    #
    @3
    @27
    vx
    @30
    @2
    @20
    wph
    @1
    @7
    @0
    cen
    breq2
    anbi1d
    exbidv
    elrab
    #
    sylibr
    @5
    @7
    ne0i
    syl
    3exp
    rexlimiv
    sylbi
    rexlimi
    con0
    cep
    wwe
    @5
    con0
    wss
    @6
    @10
    epweon
    @5
    com
    con0
    @4
    vn
    com
    ssrab2
    omsson
    sstri
    vm
    con0
    @5
    wefrc
    mp3an12
    @9
    @17
    vm
    @5
    @26
    @29
    @9
    @17
    wi
    @31
    @24
    @9
    @28
    @17
    @24
    @9
    wa
    #
    @27
    @16
    vx
    @24
    @9
    vx
    @24
    vx
    nfv
    vx
    @8
    c0
    vx
    @5
    @7
    @18
    vx
    @7
    nfcv
    nfin
    nfeq1
    nfan
    @32
    @27
    @16
    @32
    @27
    wa
    #
    wph
    @15
    @32
    @20
    wph
    simprr
    @33
    @14
    vy
    @33
    @12
    wps
    @13
    @33
    wps
    @12
    @13
    @32
    @27
    wps
    @12
    @13
    wi
    @12
    @11
    @0
    wpss
    #
    vy
    vx
    weq
    #
    wo
    @32
    @27
    wps
    wa
    #
    wa
    #
    @13
    @11
    @0
    sspss
    @37
    @34
    @13
    @35
    @37
    @34
    @13
    @24
    @9
    @36
    @34
    wn
    #
    @24
    @36
    @9
    @38
    @24
    @36
    @9
    @38
    wi
    @24
    @36
    wa
    #
    @34
    @8
    c0
    @39
    @34
    @11
    cfn
    wcel
    #
    @8
    c0
    wne
    #
    @24
    @27
    @34
    @40
    wi
    #
    wps
    @24
    @20
    @42
    wph
    @24
    @20
    wa
    #
    @21
    @42
    @20
    vm
    com
    rspe
    #
    @21
    @19
    @42
    @23
    @19
    @34
    @40
    @34
    @19
    @12
    @40
    @11
    @0
    pssss
    @0
    @11
    ssfi
    sylan2
    ex
    sylbir
    syl
    adantrr
    adantrr
    @39
    @40
    @34
    @41
    @40
    @11
    vk
    cv
    #
    cen
    wbr
    #
    vk
    com
    wrex
    @39
    @34
    @41
    wi
    #
    vk
    @11
    isfi
    @39
    @46
    @47
    vk
    com
    @39
    @45
    com
    wcel
    #
    @46
    @34
    @41
    @39
    @48
    @46
    wa
    #
    @34
    wa
    #
    wa
    #
    @45
    @8
    wcel
    #
    @41
    @51
    @48
    @0
    @45
    cen
    wbr
    #
    wph
    wa
    #
    vx
    wex
    #
    wa
    #
    @45
    @7
    wcel
    #
    wa
    #
    @52
    @51
    @48
    @55
    @57
    @39
    @48
    @46
    @34
    simprll
    @51
    @46
    wps
    @55
    @39
    @48
    @46
    @34
    simprlr
    @24
    @27
    wps
    @50
    simplrr
    @54
    @46
    wps
    wa
    vx
    @11
    vy
    vex
    @13
    @53
    @46
    wph
    wps
    @0
    @11
    @45
    cen
    breq1
    finminlem.1
    anbi12d
    spcev
    syl2anc
    @51
    @57
    @7
    @45
    wss
    #
    wn
    #
    @39
    @49
    @34
    @60
    @39
    @49
    wa
    #
    @34
    @11
    @0
    csdm
    wbr
    #
    @60
    @61
    @19
    @34
    @62
    wi
    @39
    @19
    @49
    @24
    @27
    @19
    wps
    @24
    @20
    @19
    wph
    @43
    @21
    @19
    @44
    @23
    sylibr
    adantrr
    adantrr
    adantr
    @19
    @34
    @62
    @0
    @11
    php3
    ex
    syl
    @61
    @59
    @0
    @11
    cdom
    wbr
    #
    @62
    @59
    @7
    @45
    cdom
    wbr
    #
    @61
    @63
    @45
    cvv
    wcel
    @59
    @64
    wi
    vk
    vex
    @7
    @45
    cvv
    ssdomg
    ax-mp
    @61
    @64
    @0
    @45
    cdom
    wbr
    #
    @63
    @36
    @64
    @65
    wi
    #
    @24
    @49
    @20
    @66
    wph
    wps
    @20
    @64
    @65
    @0
    @7
    @45
    endomtr
    ex
    ad2antrr
    ad2antlr
    @46
    @65
    @63
    wi
    @39
    @48
    @65
    @46
    @63
    @46
    @65
    @45
    @11
    cen
    wbr
    @63
    @11
    @45
    ensym
    @0
    @45
    @11
    domentr
    sylan2
    expcom
    ad2antll
    syld
    syl5
    @63
    @62
    @0
    @11
    domnsym
    con2i
    nsyli
    syld
    impr
    @51
    @7
    word
    #
    @45
    word
    #
    @57
    @60
    wb
    @24
    @67
    @36
    @50
    @7
    nnord
    ad2antrr
    @49
    @68
    @39
    @34
    @48
    @68
    @46
    @45
    nnord
    adantr
    ad2antrl
    @67
    @68
    wa
    @59
    @57
    @7
    @45
    ordtri1
    con2bid
    syl2anc
    mpbird
    jca31
    @52
    @45
    @5
    wcel
    #
    @57
    wa
    @58
    @45
    @5
    @7
    elin
    @69
    @56
    @57
    @4
    @55
    vn
    @45
    com
    vn
    vk
    weq
    #
    @3
    @54
    vx
    @70
    @2
    @53
    wph
    @1
    @45
    @0
    cen
    breq2
    anbi1d
    exbidv
    elrab
    anbi1i
    bitri
    sylibr
    @8
    @45
    ne0i
    syl
    exp44
    rexlimdv
    syl5bi
    com23
    mpdd
    necon2bd
    ex
    com23
    imp31
    pm2.21d
    @35
    @13
    wi
    @37
    vy
    vx
    equcomi
    a1i
    jaod
    syl5bi
    expr
    com23
    impd
    alrimiv
    jca
    ex
    eximd
    impancom
    sylbi
    rexlimiv
    3syl
end
