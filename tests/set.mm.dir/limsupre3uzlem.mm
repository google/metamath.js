include "clsp.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "wi.mm"
include "cuz.mm"
include "wss.mm"
include "uzssre.mm"
include "eqsstri.mm"
include "a1i.mm"
include "limsupre3.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "nfra1.mm"
include "simpr.mm"
include "sseldi.mm"
include "rspa.mm"
include "syldan.mm"
include "nfv.mm"
include "nfre1.mm"
include "w3a.mm"
include "eqid.mm"
include "cz.mm"
include "eluzelz2.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "eluzd.mm"
include "3adant3r.mm"
include "simp3r.mm"
include "rspe.mm"
include "syl2anc.mm"
include "3exp.mm"
include "rexlimd.mm"
include "imp.mm"
include "ralrimia.mm"
include "syl.mm"
include "cceil.mm"
include "cif.mm"
include "iftrue.mm"
include "adantl.mm"
include "ad2antrr.mm"
include "ceilcl.mm"
include "ad2antlr.mm"
include "eqeltrd.mm"
include "wn.mm"
include "iffalse.mm"
include "uzidd2.mm"
include "adantr.mm"
include "adantlr.mm"
include "pm2.61dan.mm"
include "simplr.mm"
include "fveq2.mm"
include "rexeqdv.mm"
include "rspcva.mm"
include "nfci.mm"
include "nfral.mm"
include "nfan.mm"
include "eluzelz.mm"
include "zred.mm"
include "max1.mm"
include "eluzle.mm"
include "letrd.mm"
include "3adant3.mm"
include "ceilge.mm"
include "max2.mm"
include "jca.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "ex.mm"
include "impbid.mm"
include "ralrimi.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "rexlimdva.mm"
include "sseli.mm"
include "simp1r.mm"
include "3adant1r.mm"
include "adantll.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "bitrd.mm"

theorem limsupre3uzlem
  let wph: wff ph
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vy: setvar y
  assume limsupre3uzlem.1: |- F/_ j F
  assume limsupre3uzlem.2: |- ( ph -> M e. ZZ )
  assume limsupre3uzlem.3: |- Z = ( ZZ>= ` M )
  assume limsupre3uzlem.4: |- ( ph -> F : Z --> RR* )

  disjoint F k
  disjoint F x
  disjoint k x
  disjoint M j
  disjoint M k
  disjoint j k
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint j x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint F y
  disjoint k y
  disjoint x y
  disjoint Z y
  disjoint j y
  disjoint ph y
  assert |- ( ph -> ( ( limsup ` F ) e. RR <-> ( E. x e. RR A. k e. Z E. j e. ( ZZ>= ` k ) x <_ ( F ` j ) /\ E. x e. RR E. k e. Z A. j e. ( ZZ>= ` k ) ( F ` j ) <_ x ) ) )

  proof
    wph
    cF
    clsp
    cfv
    cr
    wcel
    vy
    cv
    #
    vj
    cv
    #
    cle
    wbr
    #
    vx
    cv
    #
    @1
    cF
    cfv
    #
    cle
    wbr
    #
    wa
    #
    vj
    cZ
    wrex
    #
    vy
    cr
    wral
    #
    vx
    cr
    wrex
    #
    @2
    @4
    @3
    cle
    wbr
    #
    wi
    #
    vj
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    vx
    cr
    wrex
    #
    wa
    @5
    vj
    vk
    cv
    #
    cuz
    cfv
    #
    wrex
    #
    vk
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    @10
    vj
    @16
    wral
    #
    vk
    cZ
    wrex
    #
    vx
    cr
    wrex
    #
    wa
    wph
    vx
    cZ
    vj
    vy
    cF
    limsupre3uzlem.1
    cZ
    cr
    wss
    wph
    cZ
    cM
    cuz
    cfv
    cr
    limsupre3uzlem.3
    cM
    uzssre
    eqsstri
    #
    a1i
    limsupre3uzlem.4
    limsupre3
    wph
    @9
    @19
    @14
    @22
    wph
    @8
    @18
    vx
    cr
    wph
    @8
    @18
    @8
    @18
    wi
    wph
    @8
    @15
    @1
    cle
    wbr
    #
    @5
    wa
    #
    vj
    cZ
    wrex
    #
    vk
    cr
    wral
    #
    @18
    @8
    @27
    @7
    @26
    vy
    vk
    cr
    @0
    @15
    wceq
    #
    @6
    @25
    vj
    cZ
    @28
    @2
    @24
    @5
    @0
    @15
    @1
    cle
    breq1
    #
    anbi1d
    rexbidv
    cbvralv
    biimpi
    @27
    @17
    vk
    cZ
    @26
    vk
    cr
    nfra1
    @27
    @15
    cZ
    wcel
    #
    wa
    #
    @30
    @26
    @17
    @27
    @30
    simpr
    #
    @27
    @30
    @15
    cr
    wcel
    #
    @26
    @31
    cZ
    cr
    @15
    @23
    @32
    sseldi
    @26
    vk
    cr
    rspa
    syldan
    @30
    @26
    @17
    @30
    @25
    @17
    vj
    cZ
    @30
    vj
    nfv
    #
    @5
    vj
    @16
    nfre1
    #
    @30
    @1
    cZ
    wcel
    #
    @25
    @17
    @30
    @36
    @25
    w3a
    @1
    @16
    wcel
    #
    @5
    @17
    @30
    @36
    @24
    @37
    @5
    @30
    @36
    @24
    w3a
    @15
    @1
    @16
    @16
    eqid
    @30
    @36
    @15
    cz
    wcel
    @24
    cM
    @15
    cZ
    limsupre3uzlem.3
    eluzelz2
    3ad2ant1
    @36
    @30
    @1
    cz
    wcel
    #
    @24
    cM
    @1
    cZ
    limsupre3uzlem.3
    eluzelz2
    3ad2ant2
    @30
    @36
    @24
    simp3
    eluzd
    #
    3adant3r
    @30
    @36
    @24
    @5
    simp3r
    @5
    vj
    @16
    rspe
    syl2anc
    3exp
    rexlimd
    imp
    syl2anc
    ralrimia
    syl
    a1i
    wph
    @18
    @8
    wph
    @18
    wa
    #
    @7
    vy
    cr
    @40
    @0
    cr
    wcel
    #
    wa
    #
    @5
    vj
    cM
    @0
    cceil
    cfv
    #
    cle
    wbr
    #
    @43
    cM
    cif
    #
    cuz
    cfv
    #
    wrex
    #
    @7
    @42
    @45
    cZ
    wcel
    #
    @18
    @47
    wph
    @41
    @48
    @18
    wph
    @41
    wa
    #
    @44
    @48
    @49
    @44
    wa
    #
    @45
    @43
    cZ
    @44
    @45
    @43
    wceq
    @49
    @44
    @43
    cM
    iftrue
    adantl
    @50
    cM
    @43
    cZ
    limsupre3uzlem.3
    wph
    cM
    cz
    wcel
    #
    @41
    @44
    limsupre3uzlem.2
    ad2antrr
    @41
    @43
    cz
    wcel
    wph
    @44
    @0
    ceilcl
    #
    ad2antlr
    @49
    @44
    simpr
    eluzd
    eqeltrd
    wph
    @44
    wn
    #
    @48
    @41
    wph
    @53
    wa
    @45
    cM
    cZ
    @53
    @45
    cM
    wceq
    wph
    @44
    @43
    cM
    iffalse
    adantl
    wph
    cM
    cZ
    wcel
    @53
    wph
    cM
    cZ
    limsupre3uzlem.2
    limsupre3uzlem.3
    uzidd2
    #
    adantr
    eqeltrd
    adantlr
    pm2.61dan
    #
    adantlr
    wph
    @18
    @41
    simplr
    @17
    @47
    vk
    @45
    cZ
    @15
    @45
    wceq
    #
    @5
    vj
    @16
    @46
    @15
    @45
    cuz
    fveq2
    #
    rexeqdv
    rspcva
    syl2anc
    @42
    @5
    @7
    vj
    @46
    @40
    @41
    vj
    wph
    @18
    vj
    wph
    vj
    nfv
    #
    @17
    vj
    vk
    cZ
    vj
    vk
    cZ
    @34
    nfci
    @35
    nfral
    nfan
    @41
    vj
    nfv
    #
    nfan
    @6
    vj
    cZ
    nfre1
    wph
    @41
    @1
    @46
    wcel
    #
    @5
    @7
    wi
    wi
    @18
    @49
    @60
    @5
    @7
    @49
    @60
    @5
    w3a
    #
    @36
    @6
    @7
    @49
    @60
    @36
    @5
    @49
    @60
    wa
    #
    cM
    @1
    cZ
    limsupre3uzlem.3
    wph
    @51
    @41
    @60
    limsupre3uzlem.2
    ad2antrr
    #
    @60
    @38
    @49
    @45
    @1
    eluzelz
    adantl
    #
    @62
    cM
    @45
    @1
    @62
    cM
    @63
    zred
    @49
    @45
    cr
    wcel
    @60
    @49
    cZ
    cr
    @45
    @23
    @55
    sseldi
    #
    adantr
    #
    @62
    @1
    @64
    zred
    #
    @49
    cM
    @45
    cle
    wbr
    #
    @60
    @49
    cM
    cr
    wcel
    #
    @43
    cr
    wcel
    #
    @68
    wph
    @69
    @41
    wph
    cZ
    cr
    cM
    @23
    @54
    sseldi
    adantr
    #
    @41
    @70
    wph
    @41
    @43
    @52
    zred
    adantl
    #
    cM
    @43
    max1
    syl2anc
    adantr
    @60
    @45
    @1
    cle
    wbr
    @49
    @45
    @1
    eluzle
    adantl
    #
    letrd
    eluzd
    #
    3adant3
    @61
    @2
    @5
    @49
    @60
    @2
    @5
    @62
    @0
    @45
    @1
    wph
    @41
    @60
    simplr
    @66
    @67
    @49
    @0
    @45
    cle
    wbr
    @60
    @49
    @0
    @43
    @45
    wph
    @41
    simpr
    @72
    @65
    @41
    @0
    @43
    cle
    wbr
    wph
    @0
    ceilge
    adantl
    @49
    @69
    @70
    @43
    @45
    cle
    wbr
    @71
    @72
    cM
    @43
    max2
    syl2anc
    letrd
    adantr
    @73
    letrd
    #
    3adant3
    @49
    @60
    @5
    simp3
    jca
    @6
    vj
    cZ
    rspe
    syl2anc
    3exp
    adantlr
    rexlimd
    mpd
    ralrimiva
    ex
    impbid
    rexbidv
    wph
    @13
    @21
    vx
    cr
    wph
    @13
    @21
    wph
    @12
    @21
    vy
    cr
    @49
    @12
    @21
    @49
    @12
    wa
    #
    @48
    @10
    vj
    @46
    wral
    #
    @21
    @49
    @48
    @12
    @55
    adantr
    @76
    @10
    vj
    @46
    @49
    @12
    vj
    wph
    @41
    vj
    @58
    @59
    nfan
    @11
    vj
    cZ
    nfra1
    nfan
    @76
    @60
    @10
    @76
    @60
    wa
    #
    @2
    @10
    @49
    @60
    @2
    @12
    @75
    adantlr
    @78
    @12
    @36
    @11
    @49
    @12
    @60
    simplr
    @49
    @60
    @36
    @12
    @74
    adantlr
    @11
    vj
    cZ
    rspa
    syl2anc
    mpd
    ex
    ralrimi
    @20
    @77
    vk
    @45
    cZ
    @56
    @10
    vj
    @16
    @46
    @57
    raleqdv
    rspcev
    syl2anc
    ex
    rexlimdva
    wph
    @20
    @13
    vk
    cZ
    wph
    @30
    wa
    #
    @20
    @13
    @79
    @20
    wa
    @33
    @24
    @10
    wi
    #
    vj
    cZ
    wral
    #
    @13
    @30
    @33
    wph
    @20
    cZ
    cr
    @15
    @23
    sseli
    ad2antlr
    @30
    @20
    @81
    wph
    @30
    @20
    wa
    #
    @80
    vj
    cZ
    @30
    @20
    vj
    @34
    @10
    vj
    @16
    nfra1
    nfan
    @82
    @36
    @24
    @10
    @82
    @36
    @24
    w3a
    @20
    @37
    @10
    @30
    @20
    @36
    @24
    simp1r
    @30
    @36
    @24
    @37
    @20
    @39
    3adant1r
    @10
    vj
    @16
    rspa
    syl2anc
    3exp
    ralrimi
    adantll
    @12
    @81
    vy
    @15
    cr
    @28
    @11
    @80
    vj
    cZ
    @28
    @2
    @24
    @10
    @29
    imbi1d
    ralbidv
    rspcev
    syl2anc
    ex
    rexlimdva
    impbid
    rexbidv
    anbi12d
    bitrd
end
