include "cn.mm"
include "wcel.mm"
include "cfa.mm"
include "cfv.mm"
include "ceu.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "cabs.mm"
include "c1.mm"
include "caddc.mm"
include "cmul.mm"
include "cc.mm"
include "cn0.mm"
include "nnnn0.mm"
include "faccl.mm"
include "syl.mm"
include "nncnd.mm"
include "cc0.mm"
include "wne.mm"
include "ere.mm"
include "recni.mm"
include "epos.mm"
include "gt0ne0ii.mm"
include "divcl.mm"
include "mp3an23.mm"
include "subfacf.mm"
include "ffvelrni.mm"
include "nn0cnd.mm"
include "subcld.mm"
include "abscld.mm"
include "peano2nn.mm"
include "peano2nnd.mm"
include "nnred.mm"
include "nnmulcld.mm"
include "nndivred.mm"
include "nnrecre.mm"
include "cuz.mm"
include "cneg.mm"
include "cv.mm"
include "cexp.mm"
include "csu.mm"
include "cle.mm"
include "wbr.mm"
include "cmpt.mm"
include "eqid.mm"
include "neg1cn.mm"
include "a1i.mm"
include "ax-1cn.mm"
include "absnegi.mm"
include "abs1.mm"
include "eqtri.mm"
include "1le1.mm"
include "eqbrtri.mm"
include "eftlub.mm"
include "wa.mm"
include "wceq.mm"
include "nnnn0d.mm"
include "eluznn0.mm"
include "sylan.mm"
include "eftval.mm"
include "sumeq2dv.mm"
include "fveq2d.mm"
include "oveq1i.mm"
include "cz.mm"
include "nnzd.mm"
include "1exp.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "recnd.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "3brtr3d.mm"
include "cr.mm"
include "clt.mm"
include "wb.mm"
include "eftcl.mm"
include "mpan.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "eftlcvg.mm"
include "sylancr.mm"
include "isumcl.mm"
include "nngt0d.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "cfz.mm"
include "subfacval2.mm"
include "nncn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "eqtr4d.mm"
include "divrec.mm"
include "ce.mm"
include "df-e.mm"
include "oveq2i.mm"
include "efneg.mm"
include "ax-mp.mm"
include "efval.mm"
include "3eqtr2i.mm"
include "nn0uz.mm"
include "adantl.mm"
include "0nn0.mm"
include "mp2an.mm"
include "isumsplit.mm"
include "fzfid.mm"
include "elfznn0.mm"
include "fsumcl.mm"
include "adddid.mm"
include "3eqtrd.mm"
include "mulcld.mm"
include "subaddd.mm"
include "mpbird.mm"
include "absmuld.mm"
include "nn0ge0d.mm"
include "absidd.mm"
include "facp1.mm"
include "mulassd.mm"
include "eqtr2d.mm"
include "nnne0d.mm"
include "divcan5d.mm"
include "divassd.mm"
include "3eqtr3d.mm"
include "3brtr4d.mm"
include "nnmulcl.mm"
include "mpancom.mm"
include "ltp1d.mm"
include "adddird.mm"
include "mulcomd.mm"
include "oveq12d.mm"
include "addassd.mm"
include "breqtrrd.mm"
include "nnre.mm"
include "nngt0.mm"
include "jca.mm"
include "1red.mm"
include "lt2mul2div.mm"
include "syl22anc.mm"
include "lelttrd.mm"

theorem subfaclim
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cS: class S
  let vf: setvar f
  let vn: setvar n
  let cN: class N
  let vg: setvar g
  let vh: setvar h
  let vm: setvar m
  let vs: setvar s
  let vz: setvar z
  let cA: class A
  let vb: setvar b
  let vc: setvar c
  let cF: class F
  let vk: setvar k
  let cB: class B
  let cC: class C
  let wph: wff ph
  let cK: class K
  let cM: class M
  let cV: class V
  assume derang.d: |- D = ( x e. Fin |-> ( # ` { f | ( f : x -1-1-onto-> x /\ A. y e. x ( f ` y ) =/= y ) } ) )
  assume subfac.n: |- S = ( n e. NN0 |-> ( D ` ( 1 ... n ) ) )

  disjoint f n
  disjoint f x
  disjoint f y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint N f
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint D n
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint f g
  disjoint f h
  disjoint f m
  disjoint f s
  disjoint f z
  disjoint A f
  disjoint g h
  disjoint g m
  disjoint g n
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint h m
  disjoint h n
  disjoint h s
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n s
  disjoint n z
  disjoint A n
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint F b
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint F c
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint c h
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c z
  disjoint N c
  disjoint f k
  disjoint g k
  disjoint N g
  disjoint h k
  disjoint N h
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint N k
  disjoint N m
  disjoint N z
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b h
  disjoint b s
  disjoint b z
  disjoint B b
  disjoint c s
  disjoint B c
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B s
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C b
  disjoint C c
  disjoint C x
  disjoint C y
  disjoint b ph
  disjoint c ph
  disjoint ph x
  disjoint ph y
  disjoint K c
  disjoint K f
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint M b
  disjoint M f
  disjoint M g
  disjoint M x
  disjoint M y
  disjoint S m
  disjoint V f
  assert |- ( N e. NN -> ( abs ` ( ( ( ! ` N ) / _e ) - ( S ` N ) ) ) < ( 1 / N ) )

  proof
    cN
    cn
    wcel
    #
    cN
    cfa
    cfv
    #
    ceu
    cdiv
    co
    #
    cN
    cS
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cN
    c1
    caddc
    co
    #
    c1
    caddc
    co
    #
    @6
    @6
    cmul
    co
    #
    cdiv
    co
    #
    c1
    cN
    cdiv
    co
    #
    @0
    @4
    @0
    @2
    @3
    @0
    @1
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @0
    @1
    @0
    cN
    cn0
    wcel
    #
    @1
    cn
    wcel
    cN
    nnnn0
    #
    cN
    faccl
    syl
    #
    nncnd
    #
    @11
    ceu
    cc
    wcel
    #
    ceu
    cc0
    wne
    #
    @12
    ceu
    ere
    recni
    #
    ceu
    ere
    epos
    gt0ne0ii
    #
    @1
    ceu
    divcl
    mp3an23
    syl
    #
    @0
    @3
    @0
    @13
    @3
    cn0
    wcel
    @14
    cn0
    cn0
    cN
    cS
    vx
    vy
    cD
    cS
    vf
    vn
    derang.d
    subfac.n
    subfacf
    ffvelrni
    syl
    nn0cnd
    #
    subcld
    abscld
    @0
    @7
    @8
    @0
    @7
    @0
    @6
    cN
    peano2nn
    #
    peano2nnd
    #
    nnred
    #
    @0
    @6
    @6
    @23
    @23
    nnmulcld
    #
    nndivred
    cN
    nnrecre
    @0
    @1
    @6
    cuz
    cfv
    #
    c1
    cneg
    #
    vk
    cv
    #
    cexp
    co
    @29
    cfa
    cfv
    cdiv
    co
    #
    vk
    csu
    #
    cabs
    cfv
    #
    cmul
    co
    #
    @1
    @7
    @6
    cfa
    cfv
    #
    @6
    cmul
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    @5
    @9
    cle
    @0
    @32
    @36
    cle
    wbr
    #
    @33
    @37
    cle
    wbr
    #
    @0
    @27
    @29
    vn
    cn0
    @28
    vn
    cv
    #
    cexp
    co
    @40
    cfa
    cfv
    #
    cdiv
    co
    cmpt
    #
    cfv
    #
    vk
    csu
    #
    cabs
    cfv
    @28
    cabs
    cfv
    #
    @6
    cexp
    co
    #
    @36
    cmul
    co
    #
    @32
    @36
    cle
    @0
    @28
    vk
    vn
    @42
    vn
    cn0
    @45
    @40
    cexp
    co
    @41
    cdiv
    co
    cmpt
    #
    vn
    cn0
    @46
    @34
    cdiv
    co
    c1
    @7
    cdiv
    co
    @40
    cexp
    co
    cmul
    co
    cmpt
    #
    @6
    @42
    eqid
    #
    @48
    eqid
    @49
    eqid
    @23
    @28
    cc
    wcel
    #
    @0
    neg1cn
    a1i
    @45
    c1
    cle
    wbr
    @0
    @45
    c1
    c1
    cle
    @45
    c1
    cabs
    cfv
    c1
    c1
    ax-1cn
    absnegi
    abs1
    eqtri
    #
    1le1
    eqbrtri
    a1i
    eftlub
    @0
    @44
    @31
    cabs
    @0
    @27
    @43
    @30
    vk
    @0
    @29
    @27
    wcel
    #
    wa
    #
    @29
    cn0
    wcel
    #
    @43
    @30
    wceq
    #
    @0
    @6
    cn0
    wcel
    #
    @53
    @55
    @0
    @6
    @23
    nnnn0d
    #
    @29
    @6
    eluznn0
    sylan
    #
    @28
    vn
    @42
    @29
    @50
    eftval
    #
    syl
    #
    sumeq2dv
    fveq2d
    @0
    @47
    c1
    @36
    cmul
    co
    @36
    @0
    @46
    c1
    @36
    cmul
    @0
    @46
    c1
    @6
    cexp
    co
    #
    c1
    @45
    c1
    @6
    cexp
    @52
    oveq1i
    @0
    @6
    cz
    wcel
    @62
    c1
    wceq
    @0
    @6
    @23
    nnzd
    #
    @6
    1exp
    syl
    syl5eq
    oveq1d
    @0
    @36
    @0
    @36
    @0
    @7
    @35
    @25
    @0
    @34
    @6
    @0
    @57
    @34
    cn
    wcel
    @58
    @6
    faccl
    syl
    @23
    nnmulcld
    #
    nndivred
    #
    recnd
    mulid2d
    eqtrd
    3brtr3d
    @0
    @32
    cr
    wcel
    @36
    cr
    wcel
    @1
    cr
    wcel
    cc0
    @1
    clt
    wbr
    @38
    @39
    wb
    @0
    @31
    @0
    @30
    vk
    @42
    @6
    @27
    @27
    eqid
    #
    @63
    @61
    @54
    @55
    @30
    cc
    wcel
    #
    @59
    @51
    @55
    @67
    neg1cn
    @28
    @29
    eftcl
    #
    mpan
    #
    syl
    @0
    @51
    @57
    caddc
    @42
    @6
    cseq
    cli
    cdm
    #
    wcel
    neg1cn
    @58
    @28
    vn
    @42
    @6
    @50
    eftlcvg
    sylancr
    isumcl
    #
    abscld
    @65
    @0
    @1
    @15
    nnred
    #
    @0
    @1
    @15
    nngt0d
    @32
    @36
    @1
    lemul2
    syl112anc
    mpbid
    @0
    @5
    @1
    @31
    cmul
    co
    #
    cabs
    cfv
    @1
    cabs
    cfv
    #
    @32
    cmul
    co
    @33
    @0
    @4
    @73
    cabs
    @0
    @4
    @73
    wceq
    @3
    @73
    caddc
    co
    #
    @2
    wceq
    @0
    @75
    @1
    cc0
    @6
    c1
    cmin
    co
    #
    cfz
    co
    #
    @30
    vk
    csu
    #
    cmul
    co
    #
    @73
    caddc
    co
    #
    @2
    @0
    @3
    @79
    @73
    caddc
    @0
    @3
    @1
    cc0
    cN
    cfz
    co
    #
    @30
    vk
    csu
    #
    cmul
    co
    #
    @79
    @0
    @13
    @3
    @83
    wceq
    @14
    vx
    vy
    cD
    cS
    vf
    vk
    vn
    cN
    derang.d
    subfac.n
    subfacval2
    syl
    @0
    @78
    @82
    @1
    cmul
    @0
    @77
    @81
    @30
    vk
    @0
    @76
    cN
    cc0
    cfz
    @0
    cN
    cc
    wcel
    c1
    cc
    wcel
    #
    @76
    cN
    wceq
    cN
    nncn
    #
    ax-1cn
    cN
    c1
    pncan
    sylancl
    oveq2d
    sumeq1d
    oveq2d
    eqtr4d
    oveq1d
    @0
    @2
    @1
    c1
    ceu
    cdiv
    co
    #
    cmul
    co
    #
    @1
    @78
    @31
    caddc
    co
    #
    cmul
    co
    @80
    @0
    @11
    @2
    @87
    wceq
    #
    @16
    @11
    @17
    @18
    @89
    @19
    @20
    @1
    ceu
    divrec
    mp3an23
    syl
    @0
    @86
    @88
    @1
    cmul
    @0
    @86
    cn0
    @30
    vk
    csu
    #
    @88
    @86
    c1
    c1
    ce
    cfv
    #
    cdiv
    co
    #
    @28
    ce
    cfv
    #
    @90
    ceu
    @91
    c1
    cdiv
    df-e
    oveq2i
    @84
    @93
    @92
    wceq
    ax-1cn
    c1
    efneg
    ax-mp
    @51
    @93
    @90
    wceq
    neg1cn
    @28
    vk
    efval
    ax-mp
    3eqtr2i
    @0
    @30
    vk
    @42
    cc0
    @6
    @27
    cn0
    nn0uz
    @66
    @58
    @55
    @56
    @0
    @60
    adantl
    @55
    @67
    @0
    @69
    adantl
    caddc
    @42
    cc0
    cseq
    @70
    wcel
    #
    @0
    @51
    cc0
    cn0
    wcel
    @94
    neg1cn
    0nn0
    @28
    vn
    @42
    cc0
    @50
    eftlcvg
    mp2an
    a1i
    isumsplit
    syl5eq
    oveq2d
    @0
    @1
    @78
    @31
    @16
    @0
    @77
    @30
    vk
    @0
    cc0
    @76
    fzfid
    @0
    @29
    @77
    wcel
    #
    wa
    @51
    @55
    @67
    neg1cn
    @95
    @55
    @0
    @29
    @76
    elfznn0
    adantl
    @68
    sylancr
    fsumcl
    @71
    adddid
    3eqtrd
    eqtr4d
    @0
    @2
    @3
    @73
    @21
    @22
    @0
    @1
    @31
    @16
    @71
    mulcld
    subaddd
    mpbird
    fveq2d
    @0
    @1
    @31
    @16
    @71
    absmuld
    @0
    @74
    @1
    @32
    cmul
    @0
    @1
    @72
    @0
    @1
    @0
    @1
    @15
    nnnn0d
    nn0ge0d
    absidd
    oveq1d
    3eqtrd
    @0
    @1
    @7
    cmul
    co
    #
    @1
    @8
    cmul
    co
    #
    cdiv
    co
    @96
    @35
    cdiv
    co
    @9
    @37
    @0
    @97
    @35
    @96
    cdiv
    @0
    @35
    @1
    @6
    cmul
    co
    #
    @6
    cmul
    co
    @97
    @0
    @34
    @98
    @6
    cmul
    @0
    @13
    @34
    @98
    wceq
    @14
    cN
    facp1
    syl
    oveq1d
    @0
    @1
    @6
    @6
    @16
    @0
    @6
    @23
    nncnd
    #
    @99
    mulassd
    eqtr2d
    oveq2d
    @0
    @7
    @8
    @1
    @0
    @7
    @24
    nncnd
    #
    @0
    @8
    @26
    nncnd
    #
    @16
    @0
    @8
    @26
    nnne0d
    @0
    @1
    @15
    nnne0d
    divcan5d
    @0
    @1
    @7
    @35
    @16
    @100
    @0
    @35
    @64
    nncnd
    @0
    @35
    @64
    nnne0d
    divassd
    3eqtr3d
    3brtr4d
    @0
    @7
    cN
    cmul
    co
    #
    c1
    @8
    cmul
    co
    #
    clt
    wbr
    #
    @9
    @10
    clt
    wbr
    #
    @0
    @102
    @102
    c1
    caddc
    co
    #
    @103
    clt
    @0
    @102
    @0
    @102
    @7
    cn
    wcel
    @0
    @102
    cn
    wcel
    @24
    @7
    cN
    nnmulcl
    mpancom
    nnred
    ltp1d
    @0
    @103
    @8
    cN
    @6
    cmul
    co
    #
    c1
    @6
    cmul
    co
    #
    caddc
    co
    #
    @106
    @0
    @8
    @101
    mulid2d
    @0
    cN
    c1
    @6
    @85
    @84
    @0
    ax-1cn
    a1i
    #
    @99
    adddird
    @0
    @109
    @6
    cN
    cmul
    co
    #
    @6
    caddc
    co
    #
    @106
    @0
    @107
    @111
    @108
    @6
    caddc
    @0
    cN
    @6
    @85
    @99
    mulcomd
    @0
    @6
    @99
    mulid2d
    oveq12d
    @0
    @106
    @111
    c1
    cN
    cmul
    co
    #
    caddc
    co
    #
    c1
    caddc
    co
    @111
    cN
    caddc
    co
    #
    c1
    caddc
    co
    @112
    @0
    @102
    @114
    c1
    caddc
    @0
    @6
    c1
    cN
    @99
    @110
    @85
    adddird
    oveq1d
    @0
    @114
    @115
    c1
    caddc
    @0
    @113
    cN
    @111
    caddc
    @0
    cN
    @85
    mulid2d
    oveq2d
    oveq1d
    @0
    @111
    cN
    c1
    @0
    @6
    cN
    @99
    @85
    mulcld
    @85
    @110
    addassd
    3eqtrd
    eqtr4d
    3eqtrd
    breqtrrd
    @0
    @7
    cr
    wcel
    cN
    cr
    wcel
    #
    cc0
    cN
    clt
    wbr
    #
    wa
    c1
    cr
    wcel
    @8
    cr
    wcel
    #
    cc0
    @8
    clt
    wbr
    #
    wa
    #
    @104
    @105
    wb
    @25
    @0
    @116
    @117
    cN
    nnre
    cN
    nngt0
    jca
    @0
    1red
    @0
    @8
    cn
    wcel
    #
    @120
    @26
    @121
    @118
    @119
    @8
    nnre
    @8
    nngt0
    jca
    syl
    @7
    cN
    c1
    @8
    lt2mul2div
    syl22anc
    mpbid
    lelttrd
end
