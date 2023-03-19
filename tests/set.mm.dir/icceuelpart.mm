include "cc0.mm"
include "cfv.mm"
include "cico.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cfzo.mm"
include "wrex.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "ciccp.mm"
include "adantr.mm"
include "cn.mm"
include "iccelpart.mm"
include "syl.mm"
include "wceq.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "eleq2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "adantld.mm"
include "com12.mm"
include "mp2and.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "w3a.mm"
include "wb.mm"
include "cfz.mm"
include "elfzofz.mm"
include "adantl.mm"
include "iccpartxr.mm"
include "fzofzp1.mm"
include "jca.mm"
include "adantrr.mm"
include "elico1.mm"
include "adantrl.mm"
include "anbi12d.mm"
include "w3o.mm"
include "cr.mm"
include "elfzoelz.mm"
include "zred.mm"
include "anim12i.mm"
include "lttri4.mm"
include "icceuelpartlem.mm"
include "imp31.mm"
include "wn.mm"
include "simpl.mm"
include "nltle2tri.mm"
include "syl3anc.mm"
include "pm2.21d.mm"
include "3expd.mm"
include "ex.mm"
include "com23.mm"
include "com25.mm"
include "imp4b.mm"
include "3adant3.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "syldan.mm"
include "expcom.mm"
include "2a1.mm"
include "ancomsd.mm"
include "3adant2.mm"
include "3ad2ant2.mm"
include "3jaoi.mm"
include "mpcom.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem icceuelpart
  let wph: wff ph
  let cP: class P
  let vi: setvar i
  let cM: class M
  let cX: class X
  let vj: setvar j
  let vk: setvar k
  let vp: setvar p
  let vx: setvar x
  let cI: class I
  let cJ: class J
  assume iccpartiun.m: |- ( ph -> M e. NN )
  assume iccpartiun.p: |- ( ph -> P e. ( RePart ` M ) )

  disjoint M i
  disjoint P i
  disjoint X i
  disjoint i ph
  disjoint M j
  disjoint M k
  disjoint M p
  disjoint i j
  disjoint i k
  disjoint i p
  disjoint j k
  disjoint j p
  disjoint k p
  disjoint P j
  disjoint P k
  disjoint P p
  disjoint X p
  disjoint M x
  disjoint i x
  disjoint p x
  disjoint P x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint I i
  disjoint I j
  disjoint J j
  disjoint X j
  disjoint k x
  assert |- ( ( ph /\ X e. ( ( P ` 0 ) [,) ( P ` M ) ) ) -> E! i e. ( 0 ..^ M ) X e. ( ( P ` i ) [,) ( P ` ( i + 1 ) ) ) )

  proof
    wph
    cX
    cc0
    cP
    cfv
    #
    cM
    cP
    cfv
    #
    cico
    co
    #
    wcel
    #
    wa
    #
    cX
    vi
    cv
    #
    cP
    cfv
    #
    @5
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cico
    co
    #
    wcel
    #
    vi
    cc0
    cM
    cfzo
    co
    #
    wrex
    #
    @10
    cX
    vj
    cv
    #
    cP
    cfv
    #
    @13
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cico
    co
    #
    wcel
    #
    wa
    #
    vi
    vj
    weq
    #
    wi
    #
    vj
    @11
    wral
    vi
    @11
    wral
    #
    @10
    vi
    @11
    wreu
    @4
    cP
    cM
    ciccp
    cfv
    #
    wcel
    #
    cX
    cc0
    vp
    cv
    #
    cfv
    #
    cM
    @25
    cfv
    #
    cico
    co
    #
    wcel
    #
    cX
    @5
    @25
    cfv
    #
    @7
    @25
    cfv
    #
    cico
    co
    #
    wcel
    #
    vi
    @11
    wrex
    #
    wi
    #
    vp
    @23
    wral
    #
    @12
    wph
    @24
    @3
    iccpartiun.p
    adantr
    wph
    @36
    @3
    wph
    cM
    cn
    wcel
    #
    @36
    iccpartiun.m
    vi
    cM
    cX
    vp
    iccelpart
    syl
    adantr
    @24
    @36
    wa
    #
    @4
    @12
    @38
    @3
    @12
    wph
    @35
    @3
    @12
    wi
    vp
    cP
    @23
    @25
    cP
    wceq
    #
    @29
    @3
    @34
    @12
    @39
    @28
    @2
    cX
    @39
    @26
    @0
    @27
    @1
    cico
    cc0
    @25
    cP
    fveq1
    cM
    @25
    cP
    fveq1
    oveq12d
    eleq2d
    @39
    @33
    @10
    vi
    @11
    @39
    @32
    @9
    cX
    @39
    @30
    @6
    @31
    @8
    cico
    @5
    @25
    cP
    fveq1
    @7
    @25
    cP
    fveq1
    oveq12d
    eleq2d
    rexbidv
    imbi12d
    rspcva
    adantld
    com12
    mp2and
    wph
    @22
    @3
    wph
    @21
    vi
    vj
    @11
    @11
    wph
    @5
    @11
    wcel
    #
    @13
    @11
    wcel
    #
    wa
    #
    wa
    #
    @19
    cX
    cxr
    wcel
    #
    @6
    cX
    cle
    wbr
    #
    cX
    @8
    clt
    wbr
    #
    w3a
    #
    @44
    @14
    cX
    cle
    wbr
    #
    cX
    @16
    clt
    wbr
    #
    w3a
    #
    wa
    #
    @20
    @43
    @10
    @47
    @18
    @50
    @43
    @6
    cxr
    wcel
    #
    @8
    cxr
    wcel
    #
    wa
    #
    @10
    @47
    wb
    wph
    @40
    @54
    @41
    wph
    @40
    wa
    #
    @52
    @53
    @55
    cP
    @5
    cM
    wph
    @37
    @40
    iccpartiun.m
    adantr
    #
    wph
    @24
    @40
    iccpartiun.p
    adantr
    #
    @40
    @5
    cc0
    cM
    cfz
    co
    #
    wcel
    wph
    @5
    cc0
    cM
    elfzofz
    adantl
    iccpartxr
    #
    @55
    cP
    @7
    cM
    @56
    @57
    @40
    @7
    @58
    wcel
    wph
    cc0
    cM
    @5
    fzofzp1
    adantl
    iccpartxr
    #
    jca
    adantrr
    @6
    @8
    cX
    elico1
    syl
    @43
    @14
    cxr
    wcel
    #
    @16
    cxr
    wcel
    #
    wa
    #
    @18
    @50
    wb
    wph
    @41
    @63
    @40
    wph
    @41
    wa
    #
    @61
    @62
    @64
    cP
    @13
    cM
    wph
    @37
    @41
    iccpartiun.m
    adantr
    #
    wph
    @24
    @41
    iccpartiun.p
    adantr
    #
    @41
    @13
    @58
    wcel
    wph
    @13
    cc0
    cM
    elfzofz
    adantl
    iccpartxr
    #
    @64
    cP
    @15
    cM
    @65
    @66
    @41
    @15
    @58
    wcel
    wph
    cc0
    cM
    @13
    fzofzp1
    adantl
    iccpartxr
    #
    jca
    adantrl
    @14
    @16
    cX
    elico1
    syl
    anbi12d
    @5
    @13
    clt
    wbr
    #
    @20
    @13
    @5
    clt
    wbr
    #
    w3o
    #
    @43
    @51
    @20
    wi
    #
    @43
    @5
    cr
    wcel
    #
    @13
    cr
    wcel
    #
    wa
    #
    @71
    @42
    @75
    wph
    @40
    @73
    @41
    @74
    @40
    @5
    @5
    cc0
    cM
    elfzoelz
    zred
    @41
    @13
    @13
    cc0
    cM
    elfzoelz
    zred
    anim12i
    adantl
    @5
    @13
    lttri4
    syl
    @69
    @43
    @72
    wi
    @20
    @70
    @43
    @69
    @72
    @43
    @69
    @8
    @14
    cle
    wbr
    #
    @72
    wph
    @42
    @69
    @76
    wph
    cP
    @5
    @13
    cM
    iccpartiun.m
    iccpartiun.p
    icceuelpartlem
    imp31
    @51
    @43
    @76
    wa
    #
    @20
    @47
    @50
    @77
    @20
    wi
    #
    @46
    @44
    @50
    @78
    wi
    @45
    @50
    @46
    @78
    @44
    @48
    @46
    @78
    wi
    @49
    @44
    @48
    wa
    @77
    @46
    @20
    @44
    @48
    @43
    @76
    @46
    @20
    wi
    @44
    @46
    @43
    @76
    @48
    @20
    @44
    @43
    @46
    @76
    @48
    @20
    wi
    wi
    #
    @44
    @43
    @46
    @79
    wi
    @44
    @43
    wa
    #
    @46
    @76
    @48
    @20
    @80
    @46
    @76
    @48
    w3a
    #
    @20
    @80
    @44
    @53
    @61
    @81
    wn
    @44
    @43
    simpl
    #
    @43
    @53
    @44
    wph
    @40
    @53
    @41
    @60
    adantrr
    adantl
    @43
    @61
    @44
    wph
    @41
    @61
    @40
    @67
    adantrl
    adantl
    cX
    @8
    @14
    nltle2tri
    syl3anc
    pm2.21d
    3expd
    ex
    com23
    com25
    imp4b
    com23
    3adant3
    com12
    3ad2ant3
    imp
    com12
    syldan
    expcom
    @20
    @43
    @51
    2a1
    @43
    @70
    @72
    @43
    @70
    @16
    @6
    cle
    wbr
    #
    @72
    wph
    @42
    @70
    @83
    wph
    @41
    @40
    @70
    @83
    wi
    wph
    cP
    @13
    @5
    cM
    iccpartiun.m
    iccpartiun.p
    icceuelpartlem
    ancomsd
    imp31
    @51
    @43
    @83
    wa
    #
    @20
    @47
    @50
    @84
    @20
    wi
    #
    @45
    @44
    @50
    @85
    wi
    @46
    @50
    @45
    @85
    @44
    @49
    @45
    @85
    wi
    @48
    @44
    @49
    wa
    @84
    @45
    @20
    @44
    @49
    @43
    @83
    @45
    @20
    wi
    #
    @44
    @43
    @49
    @83
    @86
    wi
    #
    @44
    @43
    @49
    @87
    wi
    @80
    @49
    @83
    @45
    @20
    @80
    @49
    @83
    @45
    w3a
    #
    @20
    @80
    @44
    @62
    @52
    @88
    wn
    @82
    @43
    @62
    @44
    wph
    @41
    @62
    @40
    @68
    adantrl
    adantl
    @43
    @52
    @44
    wph
    @40
    @52
    @41
    @59
    adantrr
    adantl
    cX
    @16
    @6
    nltle2tri
    syl3anc
    pm2.21d
    3expd
    ex
    com23
    imp4b
    com23
    3adant2
    com12
    3ad2ant2
    imp
    com12
    syldan
    expcom
    3jaoi
    mpcom
    sylbid
    ralrimivva
    adantr
    @10
    @18
    vi
    vj
    @11
    @20
    @9
    @17
    cX
    @20
    @6
    @14
    @8
    @16
    cico
    @5
    @13
    cP
    fveq2
    @20
    @7
    @15
    cP
    @5
    @13
    c1
    caddc
    oveq1
    fveq2d
    oveq12d
    eleq2d
    reu4
    sylanbrc
end
