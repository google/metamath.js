include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "wss.mm"
include "cmpt.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "cuz.mm"
include "ciin.mm"
include "ciun.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "ssrab2f.mm"
include "a1i.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cn.mm"
include "co.mm"
include "wrex.mm"
include "c1.mm"
include "cdiv.mm"
include "caddc.mm"
include "clt.mm"
include "simpllr.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "wceq.mm"
include "fveq2.mm"
include "iineq1d.mm"
include "cbviunv.mm"
include "eleq2i.mm"
include "eliun.mm"
include "bitri.mm"
include "sylib.mm"
include "syl.mm"
include "cr.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfii1.mm"
include "nfel.mm"
include "nfmpt1.mm"
include "eqid.mm"
include "cz.mm"
include "uzssz.mm"
include "biimpi.mm"
include "sseldi.mm"
include "uzid.mm"
include "ad2antlr.mm"
include "simplll.mm"
include "simpld.mm"
include "uzss.mm"
include "syl6sseqr.mm"
include "sselda.mm"
include "ad4ant24.mm"
include "eliinid.mm"
include "adantll.mm"
include "w3a.mm"
include "cvv.mm"
include "eqidd.mm"
include "fvexd.mm"
include "fvmpt2d.mm"
include "3adant3.mm"
include "wf.mm"
include "csalg.mm"
include "adantr.mm"
include "csmblfn.mm"
include "ffvelrnda.mm"
include "smff.mm"
include "simp3.mm"
include "ffvelrnd.mm"
include "eqeltrd.mm"
include "syl3anc.mm"
include "ad5ant1345.mm"
include "rabidim2.mm"
include "climdm.mm"
include "adantl.mm"
include "sylibr.mm"
include "simpr.mm"
include "fnlimfv.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "ad4antr.mm"
include "ad5antr.mm"
include "simp-4r.mm"
include "crp.mm"
include "nnrecrp.mm"
include "climleltrp.mm"
include "simp-6l.mm"
include "simplr.mm"
include "nf3an.mm"
include "simpll.mm"
include "uztrn2.mm"
include "simpll2.mm"
include "syl2anc.mm"
include "id.mm"
include "fvmpt2.mm"
include "eqbrtrd.mm"
include "3ad2antl3.mm"
include "jca.mm"
include "rabid.mm"
include "syldan.mm"
include "adantrl.mm"
include "ex.mm"
include "ralimdaa.mm"
include "syl31anc.mm"
include "reximdva.mm"
include "mpd.mm"
include "ssrexv.mm"
include "rexlimdva.mm"
include "nfra1.mm"
include "simpll1.mm"
include "ssd.mm"
include "3adantl1.mm"
include "adantlr.mm"
include "rspa.mm"
include "cin.mm"
include "crn.mm"
include "simp1.mm"
include "simp2.mm"
include "rabexd.mm"
include "ralrimivw.mm"
include "3ad2ant1.mm"
include "elrnmpt2id.mm"
include "ovex.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "vtocl.mm"
include "ovmpt4g.mm"
include "mpbid.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "elrab.mm"
include "simprd.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "sseldd.mm"
include "ralrimi.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "ad5ant145.mm"
include "ralrimiva.mm"
include "syl6eleqr.mm"
include "rabss.mm"
include "ssind.mm"

theorem smflimlem2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cS: class S
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cM: class M
  let cZ: class Z
  let vs: setvar s
  let vr: setvar r
  let vi: setvar i
  let vj: setvar j
  assume smflimlem2.1: |- Z = ( ZZ>= ` M )
  assume smflimlem2.2: |- ( ph -> S e. SAlg )
  assume smflimlem2.3: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smflimlem2.4: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( m e. Z |-> ( ( F ` m ) ` x ) ) e. dom ~~> }
  assume smflimlem2.5: |- G = ( x e. D |-> ( ~~> ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) )
  assume smflimlem2.6: |- ( ph -> A e. RR )
  assume smflimlem2.7: |- P = ( m e. Z , k e. NN |-> { s e. S | { x e. dom ( F ` m ) | ( ( F ` m ) ` x ) < ( A + ( 1 / k ) ) } = ( s i^i dom ( F ` m ) ) } )
  assume smflimlem2.8: |- H = ( m e. Z , k e. NN |-> ( C ` ( m P k ) ) )
  assume smflimlem2.9: |- I = |^|_ k e. NN U_ n e. Z |^|_ m e. ( ZZ>= ` n ) ( m H k )
  assume smflimlem2.10: |- ( ( ph /\ r e. ran P ) -> ( C ` r ) e. r )

  disjoint A k
  disjoint A m
  disjoint A n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint A s
  disjoint k s
  disjoint m s
  disjoint C r
  disjoint D k
  disjoint D m
  disjoint D n
  disjoint F n
  disjoint F x
  disjoint n x
  disjoint F s
  disjoint s x
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint H s
  disjoint I x
  disjoint P r
  disjoint S s
  disjoint Z k
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint k x
  disjoint m x
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint k r
  disjoint m r
  disjoint ph r
  disjoint k x
  disjoint A i
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint D i
  disjoint F i
  disjoint i x
  disjoint G i
  disjoint Z i
  disjoint Z j
  disjoint j n
  disjoint i ph
  assert |- ( ph -> { x e. D | ( G ` x ) <_ A } C_ ( D i^i I ) )

  proof
    wph
    vx
    cv
    #
    cG
    cfv
    #
    cA
    cle
    wbr
    #
    vx
    cD
    crab
    #
    cD
    cI
    @3
    cD
    wss
    wph
    @2
    vx
    cD
    vx
    cD
    vm
    cZ
    @0
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    cli
    cdm
    wcel
    #
    vx
    vn
    cZ
    vm
    vn
    cv
    #
    cuz
    cfv
    #
    @5
    cdm
    #
    ciin
    #
    ciun
    #
    crab
    #
    smflimlem2.4
    @8
    vx
    @13
    nfrab1
    nfcxfr
    #
    ssrab2f
    a1i
    wph
    @2
    @0
    cI
    wcel
    #
    wi
    #
    vx
    cD
    wral
    @3
    cI
    wss
    wph
    @17
    vx
    cD
    wph
    @0
    cD
    wcel
    #
    wa
    #
    @2
    @16
    @19
    @2
    wa
    #
    @0
    vk
    cn
    vn
    cZ
    vm
    @10
    @4
    vk
    cv
    #
    cH
    co
    #
    ciin
    #
    ciun
    #
    ciin
    #
    cI
    @20
    @0
    @24
    wcel
    #
    vk
    cn
    wral
    #
    @0
    @25
    wcel
    #
    @20
    @26
    vk
    cn
    @20
    @21
    cn
    wcel
    #
    wa
    #
    @0
    @23
    wcel
    #
    vn
    cZ
    wrex
    #
    @26
    @30
    @0
    @6
    cA
    c1
    @21
    cdiv
    co
    #
    caddc
    co
    #
    clt
    wbr
    #
    vx
    @11
    crab
    #
    wcel
    #
    vm
    @10
    wral
    #
    vn
    cZ
    wrex
    #
    @32
    @30
    @0
    vm
    vi
    cv
    #
    cuz
    cfv
    #
    @11
    ciin
    #
    wcel
    #
    vi
    cZ
    wrex
    #
    @39
    @30
    @18
    @44
    wph
    @18
    @2
    @29
    simpllr
    @18
    @0
    @13
    wcel
    #
    @44
    cD
    @13
    @0
    cD
    @14
    @13
    smflimlem2.4
    @8
    vx
    @13
    ssrab2
    eqsstri
    sseli
    @45
    @0
    vi
    cZ
    @42
    ciun
    #
    wcel
    @44
    @13
    @46
    @0
    vn
    vi
    cZ
    @12
    @42
    @9
    @40
    wceq
    vm
    @10
    @41
    @11
    @9
    @40
    cuz
    fveq2
    iineq1d
    cbviunv
    eleq2i
    vi
    @0
    cZ
    @42
    eliun
    bitri
    sylib
    syl
    @30
    @43
    @39
    vi
    cZ
    @30
    @40
    cZ
    wcel
    #
    wa
    #
    @43
    @39
    @48
    @43
    wa
    #
    @38
    vn
    @41
    wrex
    #
    @39
    @49
    @4
    @7
    cfv
    #
    cr
    wcel
    #
    @51
    @34
    clt
    wbr
    #
    wa
    #
    vm
    @10
    wral
    #
    vn
    @41
    wrex
    @50
    @49
    @1
    cA
    vn
    vm
    @7
    @40
    @40
    @33
    @41
    @48
    @43
    vm
    @30
    @47
    vm
    @20
    @29
    vm
    @20
    vm
    nfv
    @29
    vm
    nfv
    nfan
    @47
    vm
    nfv
    #
    nfan
    vm
    @0
    @42
    vm
    @0
    nfcv
    vm
    @41
    @11
    nfii1
    nfel
    #
    nfan
    vm
    cZ
    @6
    nfmpt1
    @41
    eqid
    #
    @47
    @40
    @41
    wcel
    #
    @30
    @43
    @47
    @40
    cz
    wcel
    @59
    @47
    cM
    cuz
    cfv
    #
    cz
    @40
    cM
    uzssz
    @47
    @40
    @60
    wcel
    #
    cZ
    @60
    @40
    smflimlem2.1
    eleq2i
    biimpi
    #
    sseldi
    @40
    uzid
    syl
    ad2antlr
    @20
    @47
    @43
    @4
    @41
    wcel
    #
    @52
    @29
    @19
    @47
    @43
    @63
    @52
    @2
    @19
    @47
    wa
    #
    @43
    wa
    @63
    wa
    #
    wph
    @4
    cZ
    wcel
    #
    @0
    @11
    wcel
    #
    @52
    @65
    wph
    @18
    @19
    @47
    @43
    @63
    simplll
    simpld
    @47
    @63
    @66
    @19
    @43
    @47
    @41
    cZ
    @4
    @47
    @41
    @60
    cZ
    @47
    @61
    @41
    @60
    wss
    @62
    cM
    @40
    uzss
    syl
    smflimlem2.1
    syl6sseqr
    #
    sselda
    #
    ad4ant24
    @43
    @63
    @67
    @64
    vm
    @0
    @41
    @11
    eliinid
    #
    adantll
    wph
    @66
    @67
    w3a
    #
    @51
    @6
    cr
    wph
    @66
    @51
    @6
    wceq
    #
    @67
    wph
    vm
    cZ
    @6
    @7
    cvv
    wph
    @7
    eqidd
    wph
    @66
    wa
    #
    @0
    @5
    fvexd
    fvmpt2d
    3adant3
    @71
    @11
    cr
    @0
    @5
    wph
    @66
    @11
    cr
    @5
    wf
    @67
    @73
    @11
    cS
    @5
    wph
    cS
    csalg
    wcel
    @66
    smflimlem2.2
    adantr
    wph
    cZ
    cS
    csmblfn
    cfv
    @4
    cF
    smflimlem2.3
    ffvelrnda
    @11
    eqid
    smff
    3adant3
    wph
    @66
    @67
    simp3
    ffvelrnd
    eqeltrd
    syl3anc
    ad5ant1345
    ad5ant1345
    @19
    @7
    @1
    cli
    wbr
    @2
    @29
    @47
    @43
    @19
    @7
    @7
    cli
    cfv
    #
    @1
    cli
    @19
    @8
    @7
    @74
    cli
    wbr
    #
    @19
    @75
    @8
    @18
    @75
    wph
    @18
    @8
    @75
    @18
    @0
    @14
    wcel
    #
    @8
    @18
    @76
    cD
    @14
    @0
    smflimlem2.4
    eleq2i
    biimpi
    @8
    vx
    @13
    rabidim2
    syl
    @7
    climdm
    #
    sylib
    adantl
    @77
    sylibr
    @77
    sylib
    @19
    @1
    @74
    @19
    vx
    cD
    vm
    cF
    cG
    @0
    cZ
    @15
    vx
    cF
    nfcv
    smflimlem2.5
    wph
    @18
    simpr
    fnlimfv
    eqcomd
    breqtrd
    ad4antr
    wph
    cA
    cr
    wcel
    @18
    @2
    @29
    @47
    @43
    smflimlem2.6
    ad5antr
    @19
    @2
    @29
    @47
    @43
    simp-4r
    @49
    @29
    @33
    crp
    wcel
    @20
    @29
    @47
    @43
    simpllr
    @21
    nnrecrp
    syl
    climleltrp
    @49
    @55
    @38
    vn
    @41
    @49
    @9
    @41
    wcel
    #
    wa
    wph
    @47
    @43
    @78
    @55
    @38
    wi
    wph
    @18
    @2
    @29
    @47
    @43
    @78
    simp-6l
    @49
    @47
    @78
    @30
    @47
    @43
    simplr
    adantr
    @48
    @43
    @78
    simplr
    @49
    @78
    simpr
    wph
    @47
    @43
    w3a
    #
    @78
    wa
    #
    @54
    @37
    vm
    @10
    @79
    @78
    vm
    wph
    @47
    @43
    vm
    wph
    vm
    nfv
    @56
    @57
    nf3an
    @78
    vm
    nfv
    nfan
    @80
    @4
    @10
    wcel
    #
    wa
    @79
    @63
    @54
    @37
    wi
    @79
    @78
    @81
    simpll
    @78
    @81
    @63
    @79
    @40
    @4
    @9
    @41
    @58
    uztrn2
    adantll
    @79
    @63
    wa
    #
    @54
    @37
    @82
    @53
    @37
    @52
    @82
    @53
    @35
    @37
    @82
    @53
    wa
    #
    @66
    @53
    @35
    @83
    @47
    @63
    @66
    wph
    @47
    @43
    @63
    @53
    simpll2
    @79
    @63
    @53
    simplr
    @69
    syl2anc
    @82
    @53
    simpr
    @66
    @53
    wa
    @6
    @51
    @34
    clt
    @66
    @6
    @51
    wceq
    @53
    @66
    @51
    @6
    @66
    @66
    @6
    cvv
    wcel
    @72
    @66
    id
    @66
    @0
    @5
    fvexd
    vm
    cZ
    @6
    cvv
    @7
    @7
    eqid
    fvmpt2
    syl2anc
    eqcomd
    adantr
    @66
    @53
    simpr
    eqbrtrd
    syl2anc
    @82
    @35
    wa
    #
    @67
    @35
    wa
    @37
    @84
    @67
    @35
    @82
    @67
    @35
    @43
    wph
    @63
    @67
    @47
    @70
    3ad2antl3
    adantr
    @82
    @35
    simpr
    jca
    @35
    vx
    @11
    rabid
    sylibr
    syldan
    adantrl
    ex
    syl2anc
    ralimdaa
    syl31anc
    reximdva
    mpd
    @47
    @50
    @39
    wi
    #
    @30
    @43
    @47
    @41
    cZ
    wss
    @85
    @68
    @38
    vn
    @41
    cZ
    ssrexv
    syl
    ad2antlr
    mpd
    ex
    rexlimdva
    mpd
    @30
    @38
    @31
    vn
    cZ
    wph
    @29
    @9
    cZ
    wcel
    #
    @38
    @31
    wi
    @18
    @2
    wph
    @29
    @86
    w3a
    #
    @38
    @31
    @87
    @38
    wa
    #
    @0
    @22
    wcel
    #
    vm
    @10
    wral
    #
    @31
    @88
    @89
    vm
    @10
    @87
    @38
    vm
    @87
    vm
    nfv
    @37
    vm
    @10
    nfra1
    nfan
    @88
    @81
    @89
    @88
    @81
    wa
    wph
    @29
    @66
    @37
    @89
    wph
    @29
    @86
    @38
    @81
    simpll1
    wph
    @29
    @86
    @38
    @81
    simpll2
    @87
    @81
    @66
    @38
    @29
    @86
    @81
    @66
    wph
    @86
    @81
    @66
    @29
    @86
    @10
    cZ
    @4
    @86
    vj
    @10
    cZ
    cM
    vj
    cv
    @9
    cZ
    smflimlem2.1
    uztrn2
    ssd
    sselda
    adantll
    3adantl1
    adantlr
    @38
    @81
    @37
    @87
    @37
    vm
    @10
    rspa
    adantll
    wph
    @29
    @66
    w3a
    #
    @37
    wa
    @36
    @22
    @0
    @91
    @36
    @22
    wss
    @37
    @91
    @36
    @22
    @11
    cin
    #
    @22
    @91
    @22
    cS
    wcel
    #
    @36
    @92
    wceq
    #
    @91
    @22
    @36
    vs
    cv
    #
    @11
    cin
    #
    wceq
    #
    vs
    cS
    crab
    #
    wcel
    #
    @93
    @94
    wa
    @91
    @4
    @21
    cP
    co
    #
    cC
    cfv
    #
    @100
    wcel
    #
    @99
    @91
    wph
    @100
    cP
    crn
    #
    wcel
    #
    @102
    wph
    @29
    @66
    simp1
    #
    @91
    @66
    @29
    @98
    cvv
    wcel
    #
    vk
    cn
    wral
    #
    vm
    cZ
    wral
    #
    @104
    wph
    @29
    @66
    simp3
    #
    wph
    @29
    @66
    simp2
    #
    wph
    @29
    @108
    @66
    wph
    @107
    vm
    cZ
    wph
    @106
    vk
    cn
    wph
    @97
    vs
    cS
    @98
    csalg
    @98
    eqid
    smflimlem2.2
    rabexd
    #
    ralrimivw
    ralrimivw
    3ad2ant1
    vm
    vk
    cZ
    cn
    @98
    cP
    cvv
    smflimlem2.7
    elrnmpt2id
    syl3anc
    wph
    vr
    cv
    #
    @103
    wcel
    #
    wa
    #
    @112
    cC
    cfv
    #
    @112
    wcel
    #
    wi
    wph
    @104
    wa
    #
    @102
    wi
    vr
    @100
    @4
    @21
    cP
    ovex
    @112
    @100
    wceq
    #
    @114
    @117
    @116
    @102
    @118
    @113
    @104
    wph
    @112
    @100
    @103
    eleq1
    anbi2d
    @118
    @115
    @101
    @112
    @100
    @112
    @100
    cC
    fveq2
    @118
    id
    eleq12d
    imbi12d
    smflimlem2.10
    vtocl
    syl2anc
    @91
    @101
    @22
    @100
    @98
    @91
    @22
    @101
    @91
    @66
    @29
    @101
    cvv
    wcel
    @22
    @101
    wceq
    @109
    @110
    @91
    @100
    cC
    fvexd
    vm
    vk
    cZ
    cn
    @101
    cH
    cvv
    smflimlem2.8
    ovmpt4g
    syl3anc
    eqcomd
    @91
    @66
    @29
    @106
    @100
    @98
    wceq
    @109
    @110
    @91
    wph
    @106
    @105
    @111
    syl
    vm
    vk
    cZ
    cn
    @98
    cP
    cvv
    smflimlem2.7
    ovmpt4g
    syl3anc
    eleq12d
    mpbid
    @97
    @94
    vs
    @22
    cS
    @95
    @22
    wceq
    @96
    @92
    @36
    @95
    @22
    @11
    ineq1
    eqeq2d
    elrab
    sylib
    simprd
    @22
    @11
    inss1
    syl6eqss
    adantr
    @91
    @37
    simpr
    sseldd
    syl31anc
    ex
    ralrimi
    @0
    cvv
    wcel
    #
    @31
    @90
    wb
    vx
    vex
    #
    vm
    @0
    @10
    @22
    cvv
    eliin
    ax-mp
    sylibr
    ex
    ad5ant145
    reximdva
    mpd
    vn
    @0
    cZ
    @23
    eliun
    sylibr
    ralrimiva
    @119
    @28
    @27
    wb
    @120
    vk
    @0
    cn
    @24
    cvv
    eliin
    ax-mp
    sylibr
    smflimlem2.9
    syl6eleqr
    ex
    ralrimiva
    @2
    vx
    cD
    cI
    rabss
    sylibr
    ssind
end
