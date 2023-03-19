include "caddc.mm"
include "cseq.mm"
include "cvv.mm"
include "cc.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "syl6eleq.mm"
include "eluzel2.mm"
include "syl.mm"
include "serf.mm"
include "ffvelrnda.mm"
include "cabs.mm"
include "cmpt.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cli.mm"
include "cdm.mm"
include "cmul.mm"
include "wa.mm"
include "cr.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "adantr.mm"
include "remulcld.mm"
include "eqeltrd.mm"
include "fveq2d.mm"
include "fvex.mm"
include "abscld.mm"
include "recnd.mm"
include "climdm.mm"
include "sylib.mm"
include "isermulc2.mm"
include "climrel.mm"
include "releldmi.mm"
include "cc0.mm"
include "cle.mm"
include "uztrn2.mm"
include "sylan.mm"
include "absge0d.mm"
include "breqtrrd.mm"
include "syldan.mm"
include "3brtr4d.mm"
include "cvgcmp.mm"
include "climcau.mm"
include "syl2anc.mm"
include "wi.mm"
include "wf.mm"
include "serfre.mm"
include "ad2antrr.mm"
include "ffvelrnd.mm"
include "simprl.mm"
include "resubcld.mm"
include "0red.mm"
include "subcld.mm"
include "cfz.mm"
include "cdif.mm"
include "csu.mm"
include "cfn.mm"
include "wss.mm"
include "fzfid.mm"
include "difss.mm"
include "ssfi.mm"
include "sylancl.mm"
include "eldifi.mm"
include "simpll.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "syl2an.mm"
include "sylan2.mm"
include "fsumabs.mm"
include "eqidd.mm"
include "fsumser.mm"
include "oveq12d.mm"
include "cin.mm"
include "c0.mm"
include "disjdif.mm"
include "a1i.mm"
include "cun.mm"
include "undif2.mm"
include "fzss2.mm"
include "ad2antll.mm"
include "ssequn1.mm"
include "syl5req.mm"
include "fsumsplit.mm"
include "eqcomd.mm"
include "fsumcl.mm"
include "subaddd.mm"
include "mpbird.mm"
include "eqtr3d.mm"
include "abscl.mm"
include "letrd.mm"
include "absidd.mm"
include "breq1d.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "sylbid.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "seqex.mm"
include "caucvg.mm"

theorem cvgcmpce
  let wph: wff ph
  let cC: class C
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vm: setvar m
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  assume cvgcmpce.1: |- Z = ( ZZ>= ` M )
  assume cvgcmpce.2: |- ( ph -> N e. Z )
  assume cvgcmpce.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. RR )
  assume cvgcmpce.4: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. CC )
  assume cvgcmpce.5: |- ( ph -> seq M ( + , F ) e. dom ~~> )
  assume cvgcmpce.6: |- ( ph -> C e. RR )
  assume cvgcmpce.7: |- ( ( ph /\ k e. ( ZZ>= ` N ) ) -> ( abs ` ( G ` k ) ) <_ ( C x. ( F ` k ) ) )

  disjoint C k
  disjoint F k
  disjoint G k
  disjoint N k
  disjoint Z k
  disjoint M k
  disjoint k ph
  disjoint k m
  disjoint C m
  disjoint F m
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint G j
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint G m
  disjoint n x
  disjoint G n
  disjoint G x
  disjoint Z j
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint M j
  disjoint M n
  disjoint M x
  disjoint j ph
  disjoint n ph
  disjoint ph x
  assert |- ( ph -> seq M ( + , G ) e. dom ~~> )

  proof
    wph
    vx
    vj
    vn
    caddc
    cG
    cM
    cseq
    #
    cM
    cvv
    cZ
    cvgcmpce.1
    wph
    cZ
    cc
    vn
    cv
    #
    @0
    wph
    vk
    cG
    cM
    cZ
    cvgcmpce.1
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    cM
    cz
    wcel
    #
    wph
    cN
    cZ
    @2
    cvgcmpce.2
    cvgcmpce.1
    syl6eleq
    cM
    cN
    eluzel2
    syl
    #
    cvgcmpce.4
    serf
    #
    ffvelrnda
    wph
    @1
    caddc
    vm
    cZ
    vm
    cv
    #
    cG
    cfv
    #
    cabs
    cfv
    #
    cmpt
    #
    cM
    cseq
    #
    cfv
    #
    vj
    cv
    #
    @10
    cfv
    #
    cmin
    co
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
    @12
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
    @12
    @0
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @16
    clt
    wbr
    #
    vn
    @18
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
    @3
    @10
    cli
    cdm
    #
    wcel
    @21
    @4
    wph
    vk
    vm
    cZ
    cC
    @6
    cF
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    @9
    cM
    cN
    cZ
    cvgcmpce.1
    cvgcmpce.2
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @33
    @32
    cfv
    #
    cC
    @33
    cF
    cfv
    #
    cmul
    co
    #
    cr
    @34
    @36
    @38
    wceq
    #
    wph
    vm
    @33
    @31
    @38
    cZ
    @32
    @6
    @33
    wceq
    #
    @30
    @37
    cC
    cmul
    @6
    @33
    cF
    fveq2
    oveq2d
    @32
    eqid
    cC
    @37
    cmul
    ovex
    fvmpt
    #
    adantl
    #
    @35
    cC
    @37
    wph
    cC
    cr
    wcel
    @34
    cvgcmpce.6
    adantr
    cvgcmpce.3
    remulcld
    eqeltrd
    @35
    @33
    @9
    cfv
    #
    @33
    cG
    cfv
    #
    cabs
    cfv
    #
    cr
    @34
    @43
    @45
    wceq
    #
    wph
    vm
    @33
    @8
    @45
    cZ
    @9
    @40
    @7
    @44
    cabs
    @6
    @33
    cG
    fveq2
    fveq2d
    @9
    eqid
    @44
    cabs
    fvex
    fvmpt
    #
    adantl
    #
    @35
    @44
    cvgcmpce.4
    abscld
    eqeltrd
    #
    wph
    caddc
    @32
    cM
    cseq
    #
    cC
    caddc
    cF
    cM
    cseq
    #
    cli
    cfv
    #
    cmul
    co
    #
    cli
    wbr
    @50
    @29
    wcel
    wph
    @52
    cC
    vk
    cF
    @32
    cM
    cZ
    cvgcmpce.1
    @4
    wph
    cC
    cvgcmpce.6
    recnd
    wph
    @51
    @29
    wcel
    @51
    @52
    cli
    wbr
    cvgcmpce.5
    @51
    climdm
    sylib
    @35
    @37
    cvgcmpce.3
    recnd
    @42
    isermulc2
    @50
    @53
    cli
    climrel
    releldmi
    syl
    wph
    @33
    cN
    cuz
    cfv
    wcel
    #
    @34
    cc0
    @43
    cle
    wbr
    wph
    cN
    cZ
    wcel
    @54
    @34
    cvgcmpce.2
    cM
    @33
    cN
    cZ
    cvgcmpce.1
    uztrn2
    sylan
    #
    @35
    cc0
    @45
    @43
    cle
    @35
    @44
    cvgcmpce.4
    absge0d
    @48
    breqtrrd
    syldan
    wph
    @54
    wa
    #
    @45
    @38
    @43
    @36
    cle
    cvgcmpce.7
    @56
    @34
    @46
    @55
    @47
    syl
    @56
    @34
    @39
    @55
    @41
    syl
    3brtr4d
    cvgcmp
    vx
    vj
    vn
    @10
    cM
    cZ
    cvgcmpce.1
    climcau
    syl2anc
    wph
    @20
    @28
    vx
    crp
    wph
    @16
    crp
    wcel
    #
    wa
    #
    @19
    @27
    vj
    cZ
    @58
    @12
    cZ
    wcel
    #
    wa
    @17
    @26
    vn
    @18
    @58
    @59
    @1
    @18
    wcel
    #
    @17
    @26
    wi
    @58
    @59
    @60
    wa
    #
    wa
    #
    @17
    @14
    @16
    clt
    wbr
    #
    @26
    @62
    @15
    @14
    @16
    clt
    @62
    @14
    @62
    @11
    @13
    @62
    cZ
    cr
    @1
    @10
    wph
    cZ
    cr
    @10
    wf
    @57
    @61
    wph
    vk
    @9
    cM
    cZ
    cvgcmpce.1
    @4
    @49
    serfre
    ad2antrr
    #
    @61
    @1
    cZ
    wcel
    @58
    cM
    @1
    @12
    cZ
    cvgcmpce.1
    uztrn2
    adantl
    #
    ffvelrnd
    @62
    cZ
    cr
    @12
    @10
    @64
    @58
    @59
    @60
    simprl
    #
    ffvelrnd
    resubcld
    #
    @62
    cc0
    @25
    @14
    @62
    0red
    @62
    @24
    @62
    @22
    @23
    @62
    cZ
    cc
    @1
    @0
    wph
    cZ
    cc
    @0
    wf
    @57
    @61
    @5
    ad2antrr
    #
    @65
    ffvelrnd
    @62
    cZ
    cc
    @12
    @0
    @68
    @66
    ffvelrnd
    subcld
    #
    abscld
    #
    @67
    @62
    @24
    @69
    absge0d
    @62
    cM
    @1
    cfz
    co
    #
    cM
    @12
    cfz
    co
    #
    cdif
    #
    @44
    vk
    csu
    #
    cabs
    cfv
    @73
    @45
    vk
    csu
    #
    @25
    @14
    cle
    @62
    @73
    @44
    vk
    @62
    @71
    cfn
    wcel
    @73
    @71
    wss
    @73
    cfn
    wcel
    @62
    cM
    @1
    fzfid
    #
    @71
    @72
    difss
    @71
    @73
    ssfi
    sylancl
    #
    @33
    @73
    wcel
    #
    @62
    @33
    @71
    wcel
    #
    @44
    cc
    wcel
    #
    @33
    @71
    @72
    eldifi
    @62
    wph
    @34
    @80
    @79
    wph
    @57
    @61
    simpll
    #
    @79
    @33
    @2
    cZ
    @33
    cM
    @1
    elfzuz
    cvgcmpce.1
    syl6eleqr
    #
    cvgcmpce.4
    syl2an
    #
    sylan2
    #
    fsumabs
    @62
    @24
    @74
    cabs
    @62
    @71
    @44
    vk
    csu
    #
    @72
    @44
    vk
    csu
    #
    cmin
    co
    #
    @24
    @74
    @62
    @85
    @22
    @86
    @23
    cmin
    @62
    @44
    vk
    cG
    cM
    @1
    @62
    @79
    wa
    #
    @44
    eqidd
    @62
    @1
    cZ
    @2
    @65
    cvgcmpce.1
    syl6eleq
    #
    @83
    fsumser
    @62
    @44
    vk
    cG
    cM
    @12
    @62
    @33
    @72
    wcel
    #
    wa
    #
    @44
    eqidd
    @62
    @12
    cZ
    @2
    @66
    cvgcmpce.1
    syl6eleq
    #
    @62
    wph
    @34
    @80
    @90
    @81
    @90
    @33
    @2
    cZ
    @33
    cM
    @12
    elfzuz
    cvgcmpce.1
    syl6eleqr
    #
    cvgcmpce.4
    syl2an
    #
    fsumser
    oveq12d
    @62
    @87
    @74
    wceq
    @86
    @74
    caddc
    co
    #
    @85
    wceq
    @62
    @85
    @95
    @62
    @72
    @73
    @44
    @71
    vk
    @72
    @73
    cin
    c0
    wceq
    @62
    @72
    @71
    disjdif
    a1i
    #
    @62
    @72
    @73
    cun
    @72
    @71
    cun
    #
    @71
    @72
    @71
    undif2
    @62
    @72
    @71
    wss
    #
    @97
    @71
    wceq
    @60
    @98
    @58
    @59
    @12
    cM
    @1
    fzss2
    ad2antll
    @72
    @71
    ssequn1
    sylib
    syl5req
    #
    @76
    @83
    fsumsplit
    eqcomd
    @62
    @85
    @86
    @74
    @62
    @71
    @44
    vk
    @76
    @83
    fsumcl
    @62
    @72
    @44
    vk
    @62
    cM
    @12
    fzfid
    #
    @94
    fsumcl
    @62
    @73
    @44
    vk
    @77
    @84
    fsumcl
    subaddd
    mpbird
    eqtr3d
    fveq2d
    @62
    @71
    @45
    vk
    csu
    #
    @72
    @45
    vk
    csu
    #
    cmin
    co
    #
    @14
    @75
    @62
    @101
    @11
    @102
    @13
    cmin
    @62
    @45
    vk
    @9
    cM
    @1
    @88
    @34
    @46
    @79
    @34
    @62
    @82
    adantl
    @47
    syl
    @89
    @88
    @80
    @45
    cc
    wcel
    #
    @83
    @80
    @45
    @44
    abscl
    recnd
    #
    syl
    #
    fsumser
    @62
    @45
    vk
    @9
    cM
    @12
    @91
    @34
    @46
    @90
    @34
    @62
    @93
    adantl
    @47
    syl
    @92
    @91
    @80
    @104
    @94
    @105
    syl
    #
    fsumser
    oveq12d
    @62
    @103
    @75
    wceq
    @102
    @75
    caddc
    co
    #
    @101
    wceq
    @62
    @101
    @108
    @62
    @72
    @73
    @45
    @71
    vk
    @96
    @99
    @76
    @106
    fsumsplit
    eqcomd
    @62
    @101
    @102
    @75
    @62
    @71
    @45
    vk
    @76
    @106
    fsumcl
    @62
    @72
    @45
    vk
    @100
    @107
    fsumcl
    @62
    @73
    @45
    vk
    @77
    @62
    @78
    wa
    @80
    @104
    @84
    @105
    syl
    fsumcl
    subaddd
    mpbird
    eqtr3d
    3brtr4d
    #
    letrd
    absidd
    breq1d
    @62
    @25
    @14
    cle
    wbr
    #
    @63
    @26
    @109
    @62
    @25
    cr
    wcel
    @14
    cr
    wcel
    @16
    cr
    wcel
    #
    @110
    @63
    wa
    @26
    wi
    @70
    @67
    @57
    @111
    wph
    @61
    @16
    rpre
    ad2antlr
    @25
    @14
    @16
    lelttr
    syl3anc
    mpand
    sylbid
    anassrs
    ralimdva
    reximdva
    ralimdva
    mpd
    @0
    cvv
    wcel
    wph
    caddc
    cG
    cM
    seqex
    a1i
    caucvg
end
