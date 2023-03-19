include "caddc.mm"
include "cseq.mm"
include "cvv.mm"
include "wcel.mm"
include "seqex.mm"
include "a1i.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cr.mm"
include "cmin.mm"
include "co.mm"
include "wa.mm"
include "cc0.mm"
include "cli.mm"
include "climrel.mm"
include "brrelexi.mm"
include "syl.mm"
include "eqidd.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "clim0c.mm"
include "mpbid.mm"
include "c1.mm"
include "wi.mm"
include "cz.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "eluzelz.mm"
include "uzid.mm"
include "3syl.mm"
include "peano2uz.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rspcv.mm"
include "cle.mm"
include "c2.mm"
include "cdiv.mm"
include "cmul.mm"
include "ad2antll.mm"
include "zcnd.mm"
include "eleq2s.mm"
include "ad2antrl.mm"
include "subcld.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan2d.mm"
include "oveq2d.mm"
include "pncan3d.mm"
include "eqtr2d.mm"
include "adantr.mm"
include "oveq1d.mm"
include "cn0.mm"
include "simpll.mm"
include "simpl.mm"
include "ad2antlr.mm"
include "zsubcld.mm"
include "zred.mm"
include "eluzle.mm"
include "subge0d.mm"
include "mpbird.mm"
include "2re.mm"
include "2pos.mm"
include "divge0.mm"
include "syl22anc.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "w3a.mm"
include "iseraltlem3.mm"
include "simpld.mm"
include "syl3anc.mm"
include "eqbrtrd.mm"
include "2div2e1.mm"
include "oveq2i.mm"
include "cc.mm"
include "peano2cn.mm"
include "divsubdird.mm"
include "df-2.mm"
include "ax-1cn.mm"
include "pnpcan2d.mm"
include "syl5eq.mm"
include "eqtr3d.mm"
include "syl5eqr.mm"
include "subcl.mm"
include "sylancl.mm"
include "sub32d.mm"
include "3eqtrd.mm"
include "eqtrd.mm"
include "npcan.mm"
include "cn.mm"
include "uznn0sub.mm"
include "nn0p1nn.mm"
include "nnrpd.mm"
include "rphalfcld.mm"
include "rpgt0d.mm"
include "elnnz.mm"
include "nnm1nn0.mm"
include "simprd.mm"
include "wo.mm"
include "zeo.mm"
include "mpjaodan.mm"
include "wf.mm"
include "peano2uzs.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "iseraltlem1.mm"
include "sylan2.mm"
include "absidd.mm"
include "breqtrrd.mm"
include "adantlr.mm"
include "cneg.mm"
include "cexp.mm"
include "neg1rr.mm"
include "neg1ne0.mm"
include "adantl.mm"
include "reexpclzd.mm"
include "remulcld.mm"
include "eqeltrd.mm"
include "serfre.mm"
include "uztrn2.mm"
include "resubcld.mm"
include "abscld.mm"
include "rpre.mm"
include "lelttr.mm"
include "mpand.mm"
include "jctild.mm"
include "anassrs.mm"
include "ralrimdva.mm"
include "syld.mm"
include "reximdva.mm"
include "ralimdva.mm"
include "mpd.mm"
include "caurcvg2.mm"

theorem iseralt
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  let cK: class K
  let cN: class N
  assume iseralt.1: |- Z = ( ZZ>= ` M )
  assume iseralt.2: |- ( ph -> M e. ZZ )
  assume iseralt.3: |- ( ph -> G : Z --> RR )
  assume iseralt.4: |- ( ( ph /\ k e. Z ) -> ( G ` ( k + 1 ) ) <_ ( G ` k ) )
  assume iseralt.5: |- ( ph -> G ~~> 0 )
  assume iseralt.6: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = ( ( -u 1 ^ k ) x. ( G ` k ) ) )

  disjoint F k
  disjoint G k
  disjoint M k
  disjoint k ph
  disjoint Z k
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint F j
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint G j
  disjoint G n
  disjoint G x
  disjoint M j
  disjoint M n
  disjoint M x
  disjoint j ph
  disjoint n ph
  disjoint ph x
  disjoint K k
  disjoint K x
  disjoint N k
  disjoint N n
  disjoint N x
  disjoint Z j
  disjoint Z n
  disjoint Z x
  assert |- ( ph -> seq M ( + , F ) e. dom ~~> )

  proof
    wph
    vx
    vj
    vn
    caddc
    cF
    cM
    cseq
    #
    cM
    cvv
    cZ
    iseralt.1
    @0
    cvv
    wcel
    wph
    caddc
    cF
    cM
    seqex
    a1i
    wph
    vn
    cv
    #
    cG
    cfv
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vn
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    @1
    @0
    cfv
    #
    cr
    wcel
    #
    @11
    @6
    @0
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @4
    clt
    wbr
    #
    wa
    #
    vn
    @7
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    wph
    cG
    cc0
    cli
    wbr
    #
    @10
    iseralt.5
    wph
    vx
    @2
    vj
    vn
    cG
    cM
    cvv
    cZ
    iseralt.1
    iseralt.2
    wph
    @20
    cG
    cvv
    wcel
    iseralt.5
    cG
    cc0
    cli
    climrel
    brrelexi
    syl
    wph
    @1
    cZ
    wcel
    #
    wa
    #
    @2
    eqidd
    @22
    @2
    wph
    cZ
    cr
    @1
    cG
    iseralt.3
    ffvelrnda
    recnd
    clim0c
    mpbid
    wph
    @9
    @19
    vx
    crp
    wph
    @4
    crp
    wcel
    #
    wa
    #
    @8
    @18
    vj
    cZ
    @24
    @6
    cZ
    wcel
    #
    wa
    #
    @8
    @6
    c1
    caddc
    co
    #
    cG
    cfv
    #
    cabs
    cfv
    #
    @4
    clt
    wbr
    #
    @18
    @26
    @6
    @7
    wcel
    #
    @27
    @7
    wcel
    @8
    @30
    wi
    @26
    @6
    cM
    cuz
    cfv
    #
    wcel
    @6
    cz
    wcel
    #
    @31
    @26
    @6
    cZ
    @32
    @24
    @25
    simpr
    iseralt.1
    syl6eleq
    cM
    @6
    eluzelz
    #
    @6
    uzid
    3syl
    @6
    @6
    peano2uz
    @5
    @30
    vn
    @27
    @7
    @1
    @27
    wceq
    #
    @3
    @29
    @4
    clt
    @35
    @2
    @28
    cabs
    @1
    @27
    cG
    fveq2
    fveq2d
    breq1d
    rspcv
    3syl
    @26
    @30
    @17
    vn
    @7
    @24
    @25
    @1
    @7
    wcel
    #
    @30
    @17
    wi
    @24
    @25
    @36
    wa
    #
    wa
    #
    @30
    @16
    @12
    @38
    @15
    @29
    cle
    wbr
    #
    @30
    @16
    wph
    @37
    @39
    @23
    wph
    @37
    wa
    #
    @15
    @28
    @29
    cle
    @40
    @1
    @6
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    @15
    @28
    cle
    wbr
    @41
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    @40
    @43
    wa
    #
    @15
    @6
    c2
    @42
    cmul
    co
    #
    caddc
    co
    #
    @0
    cfv
    #
    @13
    cmin
    co
    #
    cabs
    cfv
    #
    @28
    cle
    @47
    @14
    @51
    cabs
    @47
    @11
    @50
    @13
    cmin
    @47
    @1
    @49
    @0
    @40
    @1
    @49
    wceq
    @43
    @40
    @49
    @6
    @41
    caddc
    co
    @1
    @40
    @48
    @41
    @6
    caddc
    @40
    @41
    c2
    @40
    @1
    @6
    @40
    @1
    @36
    @1
    cz
    wcel
    wph
    @25
    @6
    @1
    eluzelz
    ad2antll
    #
    zcnd
    #
    @40
    @6
    @25
    @33
    wph
    @36
    @33
    @6
    @32
    cZ
    @34
    iseralt.1
    eleq2s
    ad2antrl
    #
    zcnd
    #
    subcld
    #
    @40
    2cnd
    #
    c2
    cc0
    wne
    @40
    2ne0
    a1i
    #
    divcan2d
    oveq2d
    @40
    @6
    @1
    @56
    @54
    pncan3d
    eqtr2d
    adantr
    fveq2d
    oveq1d
    fveq2d
    @47
    wph
    @25
    @42
    cn0
    wcel
    #
    @52
    @28
    cle
    wbr
    #
    wph
    @37
    @43
    simpll
    @37
    @25
    wph
    @43
    @25
    @36
    simpl
    #
    ad2antlr
    @47
    @43
    cc0
    @42
    cle
    wbr
    #
    @60
    @40
    @43
    simpr
    @40
    @63
    @43
    @40
    @41
    cr
    wcel
    cc0
    @41
    cle
    wbr
    #
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    @63
    @40
    @41
    @40
    @1
    @6
    @53
    @55
    zsubcld
    #
    zred
    @40
    @64
    @6
    @1
    cle
    wbr
    #
    @36
    @68
    wph
    @25
    @6
    @1
    eluzle
    ad2antll
    @40
    @1
    @6
    @40
    @1
    @53
    zred
    @40
    @6
    @55
    zred
    subge0d
    mpbird
    @65
    @40
    2re
    a1i
    @66
    @40
    2pos
    a1i
    @41
    c2
    divge0
    syl22anc
    adantr
    @42
    elnn0z
    sylanbrc
    wph
    @25
    @60
    w3a
    @61
    @49
    c1
    caddc
    co
    @0
    cfv
    @13
    cmin
    co
    cabs
    cfv
    @28
    cle
    wbr
    wph
    vk
    cF
    cG
    @42
    cM
    @6
    cZ
    iseralt.1
    iseralt.2
    iseralt.3
    iseralt.4
    iseralt.5
    iseralt.6
    iseraltlem3
    simpld
    syl3anc
    eqbrtrd
    @40
    @46
    wa
    #
    @15
    @6
    c2
    @45
    c1
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c1
    caddc
    co
    #
    @0
    cfv
    #
    @13
    cmin
    co
    #
    cabs
    cfv
    #
    @28
    cle
    @69
    @14
    @75
    cabs
    @69
    @11
    @74
    @13
    cmin
    @69
    @1
    @73
    @0
    @40
    @1
    @73
    wceq
    @46
    @40
    @73
    @1
    c1
    cmin
    co
    #
    c1
    caddc
    co
    #
    @1
    @40
    @72
    @77
    c1
    caddc
    @40
    @72
    @6
    @77
    @6
    cmin
    co
    #
    caddc
    co
    @77
    @40
    @71
    @79
    @6
    caddc
    @40
    @71
    c2
    @41
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cmul
    co
    @80
    @79
    @40
    @70
    @81
    c2
    cmul
    @40
    @70
    @45
    c2
    c2
    cdiv
    co
    #
    cmin
    co
    #
    @81
    @82
    c1
    @45
    cmin
    2div2e1
    oveq2i
    @40
    @44
    c2
    cmin
    co
    #
    c2
    cdiv
    co
    @83
    @81
    @40
    @44
    c2
    c2
    @40
    @41
    cc
    wcel
    #
    @44
    cc
    wcel
    @57
    @41
    peano2cn
    syl
    @58
    @58
    @59
    divsubdird
    @40
    @84
    @80
    c2
    cdiv
    @40
    @84
    @44
    c1
    c1
    caddc
    co
    #
    cmin
    co
    @80
    c2
    @86
    @44
    cmin
    df-2
    oveq2i
    @40
    @41
    c1
    c1
    @57
    c1
    cc
    wcel
    #
    @40
    ax-1cn
    a1i
    #
    @88
    pnpcan2d
    syl5eq
    oveq1d
    eqtr3d
    syl5eqr
    oveq2d
    @40
    @80
    c2
    @40
    @85
    @87
    @80
    cc
    wcel
    @57
    ax-1cn
    @41
    c1
    subcl
    sylancl
    @58
    @59
    divcan2d
    @40
    @1
    @6
    c1
    @54
    @56
    @88
    sub32d
    3eqtrd
    oveq2d
    @40
    @6
    @77
    @56
    @40
    @1
    cc
    wcel
    #
    @87
    @77
    cc
    wcel
    @54
    ax-1cn
    @1
    c1
    subcl
    sylancl
    pncan3d
    eqtrd
    oveq1d
    @40
    @89
    @87
    @78
    @1
    wceq
    @54
    ax-1cn
    @1
    c1
    npcan
    sylancl
    eqtr2d
    adantr
    fveq2d
    oveq1d
    fveq2d
    @69
    wph
    @25
    @70
    cn0
    wcel
    #
    @76
    @28
    cle
    wbr
    #
    wph
    @37
    @46
    simpll
    @37
    @25
    wph
    @46
    @62
    ad2antlr
    @69
    @45
    cn
    wcel
    #
    @90
    @69
    @46
    cc0
    @45
    clt
    wbr
    #
    @92
    @40
    @46
    simpr
    @40
    @93
    @46
    @40
    @45
    @40
    @44
    @40
    @44
    @40
    @41
    cn0
    wcel
    #
    @44
    cn
    wcel
    @36
    @94
    wph
    @25
    @6
    @1
    uznn0sub
    ad2antll
    @41
    nn0p1nn
    syl
    nnrpd
    rphalfcld
    rpgt0d
    adantr
    @45
    elnnz
    sylanbrc
    @45
    nnm1nn0
    syl
    wph
    @25
    @90
    w3a
    @72
    @0
    cfv
    @13
    cmin
    co
    cabs
    cfv
    @28
    cle
    wbr
    @91
    wph
    vk
    cF
    cG
    @70
    cM
    @6
    cZ
    iseralt.1
    iseralt.2
    iseralt.3
    iseralt.4
    iseralt.5
    iseralt.6
    iseraltlem3
    simprd
    syl3anc
    eqbrtrd
    @40
    @41
    cz
    wcel
    @43
    @46
    wo
    @67
    @41
    zeo
    syl
    mpjaodan
    @40
    @28
    wph
    cZ
    cr
    cG
    wf
    @27
    cZ
    wcel
    #
    @28
    cr
    wcel
    @37
    iseralt.3
    @25
    @95
    @36
    cM
    @6
    cZ
    iseralt.1
    peano2uzs
    adantr
    #
    cZ
    cr
    @27
    cG
    ffvelrn
    syl2an
    #
    @37
    wph
    @95
    cc0
    @28
    cle
    wbr
    @96
    wph
    vk
    cG
    cM
    @27
    cZ
    iseralt.1
    iseralt.2
    iseralt.3
    iseralt.4
    iseralt.5
    iseraltlem1
    sylan2
    absidd
    #
    breqtrrd
    adantlr
    @38
    @15
    cr
    wcel
    #
    @29
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    @39
    @30
    wa
    @16
    wi
    wph
    @37
    @99
    @23
    @40
    @14
    @40
    @14
    @40
    @11
    @13
    wph
    cZ
    cr
    @0
    wf
    #
    @21
    @12
    @37
    wph
    vk
    cF
    cM
    cZ
    iseralt.1
    iseralt.2
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @103
    cF
    cfv
    c1
    cneg
    #
    @103
    cexp
    co
    #
    @103
    cG
    cfv
    #
    cmul
    co
    cr
    iseralt.6
    @105
    @107
    @108
    @105
    @106
    @103
    @106
    cr
    wcel
    @105
    neg1rr
    a1i
    @106
    cc0
    wne
    @105
    neg1ne0
    a1i
    @104
    @103
    cz
    wcel
    #
    wph
    @109
    @103
    @32
    cZ
    cM
    @103
    eluzelz
    iseralt.1
    eleq2s
    adantl
    reexpclzd
    wph
    cZ
    cr
    @103
    cG
    iseralt.3
    ffvelrnda
    remulcld
    eqeltrd
    serfre
    #
    cM
    @1
    @6
    cZ
    iseralt.1
    uztrn2
    #
    cZ
    cr
    @1
    @0
    ffvelrn
    #
    syl2an
    wph
    @102
    @25
    @13
    cr
    wcel
    @37
    @110
    @62
    cZ
    cr
    @6
    @0
    ffvelrn
    syl2an
    resubcld
    recnd
    abscld
    adantlr
    wph
    @37
    @100
    @23
    @40
    @29
    @28
    cr
    @98
    @97
    eqeltrd
    adantlr
    @23
    @101
    wph
    @37
    @4
    rpre
    ad2antlr
    @15
    @29
    @4
    lelttr
    syl3anc
    mpand
    @24
    @102
    @21
    @12
    @37
    wph
    @102
    @23
    @110
    adantr
    @111
    @112
    syl2an
    jctild
    anassrs
    ralrimdva
    syld
    reximdva
    ralimdva
    mpd
    caurcvg2
end
