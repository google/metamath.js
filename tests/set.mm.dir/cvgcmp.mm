include "caddc.mm"
include "cseq.mm"
include "cvv.mm"
include "wcel.mm"
include "seqex.mm"
include "a1i.mm"
include "cv.mm"
include "cfv.mm"
include "cc.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cr.mm"
include "cz.mm"
include "cli.mm"
include "cdm.mm"
include "syl6eleq.mm"
include "eluzel2.mm"
include "syl.mm"
include "climcau.mm"
include "syl2anc.mm"
include "wi.mm"
include "serfre.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "ralrimiva.mm"
include "r19.29uz.mm"
include "ex.mm"
include "ralimdv.mm"
include "mpd.mm"
include "uztrn2.mm"
include "sylan.mm"
include "syldan.mm"
include "adantr.mm"
include "cle.mm"
include "wf.mm"
include "simpll.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "eqid.mm"
include "adantl.mm"
include "resubcld.mm"
include "cmpt.mm"
include "simprr.mm"
include "cfz.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "eqeltrd.mm"
include "syl2an.mm"
include "c1.mm"
include "cc0.mm"
include "peano2uz.mm"
include "wb.mm"
include "subge0d.mm"
include "mpbird.mm"
include "breqtrrd.mm"
include "sylan2.mm"
include "sermono.mm"
include "sersub.mm"
include "3brtr3d.mm"
include "lesubaddd.mm"
include "mpbid.mm"
include "subsubd.mm"
include "lesubd.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "0red.mm"
include "letrd.mm"
include "abssubge0d.mm"
include "breq1d.mm"
include "3imtr4d.mm"
include "anassrs.mm"
include "adantld.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "syl6an.mm"
include "cau4.mm"
include "simpr.mm"
include "biantrurd.mm"
include "syl5ib.mm"
include "caurcvg2.mm"

theorem cvgcmp
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cZ: class Z
  let cA: class A
  let vn: setvar n
  let cB: class B
  let vm: setvar m
  let vx: setvar x
  assume cvgcmp.1: |- Z = ( ZZ>= ` M )
  assume cvgcmp.2: |- ( ph -> N e. Z )
  assume cvgcmp.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. RR )
  assume cvgcmp.4: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. RR )
  assume cvgcmp.5: |- ( ph -> seq M ( + , F ) e. dom ~~> )
  assume cvgcmp.6: |- ( ( ph /\ k e. ( ZZ>= ` N ) ) -> 0 <_ ( G ` k ) )
  assume cvgcmp.7: |- ( ( ph /\ k e. ( ZZ>= ` N ) ) -> ( G ` k ) <_ ( F ` k ) )

  disjoint F k
  disjoint G k
  disjoint k ph
  disjoint M k
  disjoint N k
  disjoint Z k
  disjoint A n
  disjoint B n
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint F m
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint Z m
  disjoint Z n
  disjoint Z x
  assert |- ( ph -> seq M ( + , G ) e. dom ~~> )

  proof
    wph
    vx
    vm
    vn
    caddc
    cG
    cM
    cseq
    #
    cM
    cvv
    cZ
    cvgcmp.1
    @0
    cvv
    wcel
    wph
    caddc
    cG
    cM
    seqex
    a1i
    wph
    vn
    cv
    #
    @0
    cfv
    #
    cc
    wcel
    #
    @2
    vm
    cv
    #
    @0
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
    wa
    #
    vn
    @4
    cuz
    cfv
    #
    wral
    #
    vm
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    @2
    cr
    wcel
    #
    @9
    wa
    #
    vn
    @11
    wral
    #
    vm
    cZ
    wrex
    #
    vx
    crp
    wral
    wph
    @1
    caddc
    cF
    cM
    cseq
    #
    cfv
    #
    cc
    wcel
    #
    @20
    @4
    @19
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @8
    clt
    wbr
    #
    wa
    #
    vn
    @11
    wral
    #
    vm
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    @14
    wph
    @25
    vn
    @11
    wral
    vm
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    @29
    wph
    cM
    cz
    wcel
    #
    @19
    cli
    cdm
    wcel
    @31
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    @32
    wph
    cN
    cZ
    @33
    cvgcmp.2
    cvgcmp.1
    syl6eleq
    cM
    cN
    eluzel2
    syl
    #
    cvgcmp.5
    vx
    vm
    vn
    @19
    cM
    cZ
    cvgcmp.1
    climcau
    syl2anc
    wph
    @30
    @28
    vx
    crp
    wph
    @21
    vn
    cZ
    wral
    #
    @30
    @28
    wi
    wph
    @21
    vn
    cZ
    wph
    @1
    cZ
    wcel
    #
    wa
    #
    @20
    wph
    cZ
    cr
    @1
    @19
    wph
    vk
    cF
    cM
    cZ
    cvgcmp.1
    @34
    cvgcmp.3
    serfre
    #
    ffvelrnda
    #
    recnd
    ralrimiva
    @35
    @30
    @28
    @21
    @25
    vm
    vn
    cM
    cZ
    cvgcmp.1
    r19.29uz
    ex
    syl
    ralimdv
    mpd
    wph
    @27
    vm
    cN
    cuz
    cfv
    #
    wrex
    #
    vx
    crp
    wral
    #
    @12
    vm
    @40
    wrex
    #
    vx
    crp
    wral
    #
    @29
    @14
    wph
    @41
    @43
    vx
    crp
    wph
    @8
    crp
    wcel
    #
    wa
    #
    @3
    vn
    @40
    wral
    #
    @41
    @9
    vn
    @11
    wral
    #
    vm
    @40
    wrex
    @43
    wph
    @47
    @45
    wph
    @3
    vn
    @40
    wph
    @1
    @40
    wcel
    #
    @36
    @3
    wph
    cN
    cZ
    wcel
    #
    @49
    @36
    cvgcmp.2
    cM
    @1
    cN
    cZ
    cvgcmp.1
    uztrn2
    #
    sylan
    @37
    @2
    wph
    cZ
    cr
    @1
    @0
    wph
    vk
    cG
    cM
    cZ
    cvgcmp.1
    @34
    cvgcmp.4
    serfre
    #
    ffvelrnda
    #
    recnd
    syldan
    ralrimiva
    adantr
    @46
    @27
    @48
    vm
    @40
    @46
    @4
    @40
    wcel
    #
    wa
    #
    @26
    @9
    vn
    @11
    @55
    @1
    @11
    wcel
    #
    wa
    @25
    @9
    @21
    @46
    @54
    @56
    @25
    @9
    wi
    @46
    @54
    @56
    wa
    #
    wa
    #
    @23
    @8
    clt
    wbr
    #
    @6
    @8
    clt
    wbr
    #
    @25
    @9
    @58
    @6
    @23
    cle
    wbr
    #
    @59
    @60
    @58
    @22
    @20
    @6
    @58
    cZ
    cr
    @4
    @19
    @58
    wph
    cZ
    cr
    @19
    wf
    wph
    @45
    @57
    simpll
    #
    @38
    syl
    @58
    @50
    @54
    @4
    cZ
    wcel
    #
    @58
    wph
    @50
    @62
    cvgcmp.2
    syl
    #
    @46
    @54
    @56
    simprl
    #
    cM
    @4
    cN
    cZ
    cvgcmp.1
    uztrn2
    syl2anc
    #
    ffvelrnd
    #
    @58
    wph
    @36
    @20
    cr
    wcel
    @62
    @58
    @50
    @49
    @36
    @64
    @57
    @49
    @46
    cN
    @1
    @4
    @40
    @40
    eqid
    #
    uztrn2
    adantl
    @51
    syl2anc
    #
    @39
    syl2anc
    #
    @58
    @2
    @5
    @58
    wph
    @36
    @15
    @62
    @69
    @53
    syl2anc
    #
    @58
    cZ
    cr
    @4
    @0
    @58
    wph
    cZ
    cr
    @0
    wf
    @62
    @52
    syl
    @66
    ffvelrnd
    #
    resubcld
    #
    @58
    @22
    @20
    @2
    cmin
    co
    #
    @5
    caddc
    co
    #
    @20
    @6
    cmin
    co
    cle
    @58
    @22
    @5
    cmin
    co
    #
    @74
    cle
    wbr
    @22
    @75
    cle
    wbr
    @58
    @4
    caddc
    vm
    cZ
    @4
    cF
    cfv
    #
    @4
    cG
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    cM
    cseq
    #
    cfv
    @1
    @81
    cfv
    @76
    @74
    cle
    @58
    vk
    @80
    @4
    cM
    @1
    @58
    @4
    cZ
    @33
    @66
    cvgcmp.1
    syl6eleq
    #
    @46
    @54
    @56
    simprr
    #
    @58
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    @84
    @80
    cfv
    #
    cr
    wcel
    @84
    cM
    @1
    cfz
    co
    wcel
    #
    @62
    @87
    @84
    @33
    cZ
    @84
    cM
    @1
    elfzuz
    cvgcmp.1
    syl6eleqr
    #
    wph
    @85
    wa
    #
    @86
    @84
    cF
    cfv
    #
    @84
    cG
    cfv
    #
    cmin
    co
    #
    cr
    @85
    @86
    @92
    wceq
    #
    wph
    vm
    @84
    @79
    @92
    cZ
    @80
    @4
    @84
    wceq
    @77
    @90
    @78
    @91
    cmin
    @4
    @84
    cF
    fveq2
    @4
    @84
    cG
    fveq2
    oveq12d
    @80
    eqid
    @90
    @91
    cmin
    ovex
    fvmpt
    #
    adantl
    #
    @89
    @90
    @91
    cvgcmp.3
    cvgcmp.4
    resubcld
    eqeltrd
    syl2an
    @84
    @4
    c1
    caddc
    co
    #
    @1
    cfz
    co
    wcel
    #
    @58
    @84
    @96
    cuz
    cfv
    wcel
    #
    cc0
    @86
    cle
    wbr
    #
    @84
    @96
    @1
    elfzuz
    #
    @58
    @98
    @84
    @40
    wcel
    #
    @99
    @58
    @96
    @40
    wcel
    #
    @98
    @101
    @58
    @54
    @102
    @65
    cN
    @4
    peano2uz
    syl
    cN
    @84
    @96
    @40
    @68
    uztrn2
    sylan
    #
    @58
    wph
    @101
    @99
    @62
    wph
    @101
    wa
    #
    cc0
    @92
    @86
    cle
    @104
    cc0
    @92
    cle
    wbr
    #
    @91
    @90
    cle
    wbr
    #
    cvgcmp.7
    wph
    @101
    @85
    @105
    @106
    wb
    wph
    @50
    @101
    @85
    cvgcmp.2
    cM
    @84
    cN
    cZ
    cvgcmp.1
    uztrn2
    sylan
    #
    @89
    @90
    @91
    cvgcmp.3
    cvgcmp.4
    subge0d
    syldan
    mpbird
    @104
    @85
    @93
    @107
    @94
    syl
    breqtrrd
    sylan
    syldan
    sylan2
    sermono
    @58
    vk
    cF
    cG
    @80
    cM
    @4
    @82
    @58
    wph
    @85
    @90
    cc
    wcel
    #
    @84
    cM
    @4
    cfz
    co
    wcel
    #
    @62
    @109
    @84
    @33
    cZ
    @84
    cM
    @4
    elfzuz
    cvgcmp.1
    syl6eleqr
    #
    @89
    @90
    cvgcmp.3
    recnd
    #
    syl2an
    @58
    wph
    @85
    @91
    cc
    wcel
    #
    @109
    @62
    @110
    @89
    @91
    cvgcmp.4
    recnd
    #
    syl2an
    @58
    wph
    @85
    @93
    @109
    @62
    @110
    @95
    syl2an
    sersub
    @58
    vk
    cF
    cG
    @80
    cM
    @1
    @58
    @1
    cZ
    @33
    @69
    cvgcmp.1
    syl6eleq
    @58
    wph
    @85
    @108
    @87
    @62
    @88
    @111
    syl2an
    @58
    wph
    @85
    @112
    @87
    @62
    @88
    @113
    syl2an
    @58
    wph
    @85
    @93
    @87
    @62
    @88
    @95
    syl2an
    sersub
    3brtr3d
    @58
    @22
    @5
    @74
    @67
    @72
    @58
    @20
    @2
    @70
    @71
    resubcld
    lesubaddd
    mpbid
    @58
    @20
    @2
    @5
    @58
    @20
    @70
    recnd
    @58
    @2
    @71
    recnd
    @58
    @5
    @72
    recnd
    subsubd
    breqtrrd
    lesubd
    @58
    @6
    cr
    wcel
    @23
    cr
    wcel
    @8
    cr
    wcel
    #
    @61
    @59
    wa
    @60
    wi
    @73
    @58
    @20
    @22
    @70
    @67
    resubcld
    @45
    @114
    wph
    @57
    @8
    rpre
    ad2antlr
    @6
    @23
    @8
    lelttr
    syl3anc
    mpand
    @58
    @24
    @23
    @8
    clt
    @58
    @22
    @20
    @67
    @70
    @58
    vk
    cF
    @4
    cM
    @1
    @82
    @83
    @58
    wph
    @85
    @90
    cr
    wcel
    #
    @87
    @62
    @88
    cvgcmp.3
    syl2an
    @58
    @97
    @101
    cc0
    @90
    cle
    wbr
    #
    @97
    @58
    @98
    @101
    @100
    @103
    sylan2
    @58
    wph
    @101
    @116
    @62
    @104
    cc0
    @91
    @90
    @104
    0red
    wph
    @101
    @85
    @91
    cr
    wcel
    #
    @107
    cvgcmp.4
    syldan
    wph
    @101
    @85
    @115
    @107
    cvgcmp.3
    syldan
    cvgcmp.6
    cvgcmp.7
    letrd
    sylan
    syldan
    sermono
    abssubge0d
    breq1d
    @58
    @7
    @6
    @8
    clt
    @58
    @5
    @2
    @72
    @71
    @58
    vk
    cG
    @4
    cM
    @1
    @82
    @83
    @58
    wph
    @85
    @117
    @87
    @62
    @88
    cvgcmp.4
    syl2an
    @97
    @58
    @98
    cc0
    @91
    cle
    wbr
    #
    @100
    @58
    @98
    @101
    @118
    @103
    @58
    wph
    @101
    @118
    @62
    cvgcmp.6
    sylan
    syldan
    sylan2
    sermono
    abssubge0d
    breq1d
    3imtr4d
    anassrs
    adantld
    ralimdva
    reximdva
    @3
    @9
    vm
    vn
    cN
    @40
    @68
    r19.29uz
    syl6an
    ralimdva
    wph
    @50
    @29
    @42
    wb
    cvgcmp.2
    vx
    vm
    vn
    @19
    cM
    cN
    @40
    cZ
    cvgcmp.1
    @68
    cau4
    syl
    wph
    @50
    @14
    @44
    wb
    cvgcmp.2
    vx
    vm
    vn
    @0
    cM
    cN
    @40
    cZ
    cvgcmp.1
    @68
    cau4
    syl
    3imtr4d
    mpd
    wph
    @13
    @18
    vx
    crp
    wph
    @12
    @17
    vm
    cZ
    wph
    @63
    wa
    @10
    @16
    vn
    @11
    wph
    @63
    @56
    @10
    @16
    wi
    #
    @63
    @56
    wa
    wph
    @36
    @119
    cM
    @1
    @4
    cZ
    cvgcmp.1
    uztrn2
    @10
    @9
    @37
    @16
    @3
    @9
    simpr
    @37
    @15
    @9
    @53
    biantrurd
    syl5ib
    sylan2
    anassrs
    ralimdva
    reximdva
    ralimdv
    mpd
    caurcvg2
end
