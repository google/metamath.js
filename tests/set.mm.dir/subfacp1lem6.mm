include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "cfz.mm"
include "crab.mm"
include "chash.mm"
include "cmin.mm"
include "cmul.mm"
include "cn0.mm"
include "wceq.mm"
include "peano2nn.mm"
include "nnnn0d.mm"
include "subfacval.mm"
include "syl.mm"
include "wf1o.mm"
include "wne.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "cfn.mm"
include "fzfid.mm"
include "derangval.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "wss.mm"
include "wf.mm"
include "cuz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "f1of.mm"
include "adantr.mm"
include "ffvelrn.mm"
include "expcom.mm"
include "syl2im.mm"
include "ss2abdv.mm"
include "weq.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "cbvabv.mm"
include "3sstr4g.mm"
include "ssabral.mm"
include "sylib.mm"
include "rabid2.mm"
include "sylibr.mm"
include "fveq2d.mm"
include "3eqtrd.mm"
include "elfz1end.mm"
include "wi.mm"
include "cc0.mm"
include "eleq1.mm"
include "csn.mm"
include "oveq2.mm"
include "cz.mm"
include "1z.mm"
include "fzsn.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "fvex.mm"
include "elsn.mm"
include "syl6bb.mm"
include "rabbidv.mm"
include "oveq1.mm"
include "1m1e0.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "c0.mm"
include "hash0.mm"
include "wn.mm"
include "fveq2.mm"
include "id.mm"
include "neeq12d.mm"
include "rspcv.mm"
include "adantld.mm"
include "df-ne.mm"
include "neeq1d.mm"
include "syl5bbr.mm"
include "rabeq0.mm"
include "nnnn0.mm"
include "subfacf.mm"
include "ffvelrni.mm"
include "nnm1nn0.mm"
include "nn0addcld.mm"
include "nn0cnd.mm"
include "mul02d.mm"
include "3eqtr4a.mm"
include "a1d.mm"
include "simplr.mm"
include "peano2fzr.mm"
include "sylancom.mm"
include "ex.mm"
include "imim1d.mm"
include "cun.mm"
include "wo.mm"
include "wb.mm"
include "elfzp1.mm"
include "unrab.mm"
include "cin.mm"
include "fzfi.mm"
include "deranglem.mm"
include "eqeltri.mm"
include "ssrab2.mm"
include "ssfi.mm"
include "mp2an.mm"
include "inrab.mm"
include "fzp1disj.mm"
include "inelcm.mm"
include "sylan2br.mm"
include "necon2bi.mm"
include "rgenw.mm"
include "mpbir.mm"
include "eqtri.mm"
include "hashun.mm"
include "mp3an.mm"
include "cc.mm"
include "nncn.mm"
include "ad2antlr.mm"
include "ax-1cn.mm"
include "a1i.mm"
include "addsubd.mm"
include "subcl.mm"
include "sylancl.mm"
include "ad2antrr.mm"
include "adddird.mm"
include "mulid2d.mm"
include "exmidne.mm"
include "orcom.mm"
include "mpbi.mm"
include "biantru.mm"
include "andi.mm"
include "bitri.mm"
include "rabbii.mm"
include "eqtr4i.mm"
include "simpr.mm"
include "necon3ai.mm"
include "adantl.mm"
include "imnan.mm"
include "c2.mm"
include "cid.mm"
include "cdif.mm"
include "cres.mm"
include "cop.mm"
include "cpr.mm"
include "simpll.mm"
include "nnne0.mm"
include "0p1e1.mm"
include "eqeq2i.mm"
include "0cn.mm"
include "addcan2.mm"
include "mp3an23.mm"
include "necon3bbid.mm"
include "mpbird.mm"
include "elfzp12.mm"
include "biimpa.mm"
include "ord.mm"
include "mpd.mm"
include "df-2.mm"
include "oveq1i.mm"
include "syl6eleqr.mm"
include "ovex.mm"
include "eqid.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "cbvrabv.mm"
include "f1oeq1.mm"
include "cbvralv.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "subfacp1lem5.mm"
include "subfacp1lem3.mm"
include "oveq12d.mm"
include "syl5eq.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "syl5ibr.mm"
include "a2d.mm"
include "syld.mm"
include "nnind.mm"
include "mpcom.mm"
include "pncan.mm"

theorem subfacp1lem6
  let vx: setvar x
  let vy: setvar y
  let cA: class A
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
  assume subfacp1lem.a: |- A = { f | ( f : ( 1 ... ( N + 1 ) ) -1-1-onto-> ( 1 ... ( N + 1 ) ) /\ A. y e. ( 1 ... ( N + 1 ) ) ( f ` y ) =/= y ) }

  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
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
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x z
  disjoint y z
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
  assert |- ( N e. NN -> ( S ` ( N + 1 ) ) = ( N x. ( ( S ` N ) + ( S ` ( N - 1 ) ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c1
    caddc
    co
    #
    cS
    cfv
    #
    c1
    vg
    cv
    #
    cfv
    #
    c1
    @1
    cfz
    co
    #
    wcel
    #
    vg
    cA
    crab
    #
    chash
    cfv
    #
    @1
    c1
    cmin
    co
    #
    cN
    cS
    cfv
    #
    cN
    c1
    cmin
    co
    #
    cS
    cfv
    #
    caddc
    co
    #
    cmul
    co
    #
    cN
    @13
    cmul
    co
    @0
    @2
    @5
    cD
    cfv
    #
    cA
    chash
    cfv
    #
    @8
    @0
    @1
    cn0
    wcel
    @2
    @15
    wceq
    @0
    @1
    cN
    peano2nn
    #
    nnnn0d
    vx
    vy
    cD
    cS
    vf
    vn
    @1
    derang.d
    subfac.n
    subfacval
    syl
    @0
    @15
    @5
    @5
    vf
    cv
    #
    wf1o
    #
    vy
    cv
    #
    @18
    cfv
    #
    @20
    wne
    #
    vy
    @5
    wral
    #
    wa
    #
    vf
    cab
    #
    chash
    cfv
    #
    @16
    @0
    @5
    cfn
    wcel
    #
    @15
    @26
    wceq
    @0
    c1
    @1
    fzfid
    vx
    vy
    @5
    cD
    vf
    derang.d
    derangval
    syl
    cA
    @25
    chash
    subfacp1lem.a
    fveq2i
    syl6eqr
    @0
    cA
    @7
    chash
    @0
    @6
    vg
    cA
    wral
    #
    cA
    @7
    wceq
    @0
    cA
    @6
    vg
    cab
    #
    wss
    @28
    @0
    @25
    c1
    @18
    cfv
    #
    @5
    wcel
    #
    vf
    cab
    cA
    @29
    @0
    @24
    @31
    vf
    @0
    c1
    @5
    wcel
    #
    @24
    @5
    @5
    @18
    wf
    #
    @31
    @0
    @1
    c1
    cuz
    cfv
    #
    wcel
    #
    @32
    @0
    @1
    cn
    @34
    @17
    nnuz
    syl6eleq
    #
    c1
    @1
    eluzfz1
    syl
    #
    @19
    @33
    @23
    @5
    @5
    @18
    f1of
    adantr
    @33
    @32
    @31
    @5
    @5
    c1
    @18
    ffvelrn
    expcom
    syl2im
    ss2abdv
    subfacp1lem.a
    @6
    @31
    vg
    vf
    vg
    vf
    weq
    #
    @4
    @30
    @5
    c1
    @3
    @18
    fveq1
    #
    eleq1d
    cbvabv
    3sstr4g
    @6
    vg
    cA
    ssabral
    sylib
    @6
    vg
    cA
    rabid2
    sylibr
    fveq2d
    3eqtrd
    @0
    @1
    @5
    wcel
    #
    @8
    @14
    wceq
    #
    @0
    @1
    cn
    wcel
    #
    @40
    @17
    @1
    elfz1end
    sylib
    @42
    @0
    @40
    @41
    wi
    #
    @17
    @0
    vx
    cv
    #
    @5
    wcel
    #
    @4
    c1
    @44
    cfz
    co
    #
    wcel
    #
    vg
    cA
    crab
    #
    chash
    cfv
    #
    @44
    c1
    cmin
    co
    #
    @13
    cmul
    co
    #
    wceq
    #
    wi
    #
    wi
    @0
    @32
    @4
    c1
    wceq
    #
    vg
    cA
    crab
    #
    chash
    cfv
    #
    cc0
    @13
    cmul
    co
    #
    wceq
    #
    wi
    #
    wi
    @0
    vm
    cv
    #
    @5
    wcel
    #
    @4
    c1
    @60
    cfz
    co
    #
    wcel
    #
    vg
    cA
    crab
    #
    chash
    cfv
    #
    @60
    c1
    cmin
    co
    #
    @13
    cmul
    co
    #
    wceq
    #
    wi
    #
    wi
    @0
    @60
    c1
    caddc
    co
    #
    @5
    wcel
    #
    @4
    c1
    @70
    cfz
    co
    #
    wcel
    #
    vg
    cA
    crab
    #
    chash
    cfv
    #
    @70
    c1
    cmin
    co
    #
    @13
    cmul
    co
    #
    wceq
    #
    wi
    #
    wi
    @0
    @43
    wi
    vx
    vm
    @1
    @44
    c1
    wceq
    #
    @53
    @59
    @0
    @80
    @45
    @32
    @52
    @58
    @44
    c1
    @5
    eleq1
    @80
    @49
    @56
    @51
    @57
    @80
    @48
    @55
    chash
    @80
    @47
    @54
    vg
    cA
    @80
    @47
    @4
    c1
    csn
    #
    wcel
    @54
    @80
    @46
    @81
    @4
    @80
    @46
    c1
    c1
    cfz
    co
    #
    @81
    @44
    c1
    c1
    cfz
    oveq2
    c1
    cz
    wcel
    @82
    @81
    wceq
    1z
    c1
    fzsn
    ax-mp
    syl6eq
    eleq2d
    @4
    c1
    c1
    @3
    fvex
    #
    elsn
    syl6bb
    rabbidv
    fveq2d
    @80
    @50
    cc0
    @13
    cmul
    @80
    @50
    c1
    c1
    cmin
    co
    cc0
    @44
    c1
    c1
    cmin
    oveq1
    1m1e0
    syl6eq
    oveq1d
    eqeq12d
    imbi12d
    imbi2d
    vx
    vm
    weq
    #
    @53
    @69
    @0
    @84
    @45
    @61
    @52
    @68
    @44
    @60
    @5
    eleq1
    @84
    @49
    @65
    @51
    @67
    @84
    @48
    @64
    chash
    @84
    @47
    @63
    vg
    cA
    @84
    @46
    @62
    @4
    @44
    @60
    c1
    cfz
    oveq2
    eleq2d
    rabbidv
    fveq2d
    @84
    @50
    @66
    @13
    cmul
    @44
    @60
    c1
    cmin
    oveq1
    oveq1d
    eqeq12d
    imbi12d
    imbi2d
    @44
    @70
    wceq
    #
    @53
    @79
    @0
    @85
    @45
    @71
    @52
    @78
    @44
    @70
    @5
    eleq1
    @85
    @49
    @75
    @51
    @77
    @85
    @48
    @74
    chash
    @85
    @47
    @73
    vg
    cA
    @85
    @46
    @72
    @4
    @44
    @70
    c1
    cfz
    oveq2
    eleq2d
    rabbidv
    fveq2d
    @85
    @50
    @76
    @13
    cmul
    @44
    @70
    c1
    cmin
    oveq1
    oveq1d
    eqeq12d
    imbi12d
    imbi2d
    @44
    @1
    wceq
    #
    @53
    @43
    @0
    @86
    @45
    @40
    @52
    @41
    @44
    @1
    @5
    eleq1
    @86
    @49
    @8
    @51
    @14
    @86
    @48
    @7
    chash
    @86
    @47
    @6
    vg
    cA
    @86
    @46
    @5
    @4
    @44
    @1
    c1
    cfz
    oveq2
    eleq2d
    rabbidv
    fveq2d
    @86
    @50
    @9
    @13
    cmul
    @44
    @1
    c1
    cmin
    oveq1
    oveq1d
    eqeq12d
    imbi12d
    imbi2d
    @0
    @58
    @32
    @0
    c0
    chash
    cfv
    cc0
    @56
    @57
    hash0
    @0
    @55
    c0
    chash
    @0
    @54
    wn
    #
    vg
    cA
    wral
    #
    @55
    c0
    wceq
    @0
    cA
    @87
    vg
    cab
    #
    wss
    @88
    @0
    @25
    @30
    c1
    wne
    #
    vf
    cab
    cA
    @89
    @0
    @24
    @90
    vf
    @0
    @23
    @90
    @19
    @0
    @32
    @23
    @90
    wi
    @37
    @22
    @90
    vy
    c1
    @5
    @20
    c1
    wceq
    #
    @21
    @30
    @20
    c1
    @20
    c1
    @18
    fveq2
    @91
    id
    neeq12d
    rspcv
    syl
    adantld
    ss2abdv
    subfacp1lem.a
    @87
    @90
    vg
    vf
    @87
    @4
    c1
    wne
    @38
    @90
    @4
    c1
    df-ne
    @38
    @4
    @30
    c1
    @39
    neeq1d
    syl5bbr
    cbvabv
    3sstr4g
    @87
    vg
    cA
    ssabral
    sylib
    @54
    vg
    cA
    rabeq0
    sylibr
    fveq2d
    @0
    @13
    @0
    @13
    @0
    @10
    @12
    @0
    cN
    cn0
    wcel
    @10
    cn0
    wcel
    cN
    nnnn0
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
    #
    ffvelrni
    syl
    @0
    @11
    cn0
    wcel
    @12
    cn0
    wcel
    cN
    nnm1nn0
    cn0
    cn0
    @11
    cS
    @92
    ffvelrni
    syl
    nn0addcld
    #
    nn0cnd
    mul02d
    3eqtr4a
    a1d
    @60
    cn
    wcel
    #
    @0
    @69
    @79
    @0
    @94
    @69
    @79
    wi
    @0
    @94
    wa
    #
    @69
    @71
    @68
    wi
    @79
    @95
    @71
    @61
    @68
    @95
    @71
    @61
    @95
    @71
    @60
    @34
    wcel
    #
    @61
    @95
    @71
    wa
    #
    @60
    cn
    @34
    @0
    @94
    @71
    simplr
    nnuz
    syl6eleq
    #
    @60
    c1
    @1
    peano2fzr
    sylancom
    ex
    imim1d
    @95
    @71
    @68
    @78
    @95
    @71
    @68
    @78
    wi
    @68
    @78
    @97
    @65
    @4
    @70
    wceq
    #
    vg
    cA
    crab
    #
    chash
    cfv
    #
    caddc
    co
    #
    @67
    @101
    caddc
    co
    #
    wceq
    @65
    @67
    @101
    caddc
    oveq1
    @97
    @75
    @102
    @77
    @103
    @97
    @75
    @64
    @100
    cun
    #
    chash
    cfv
    #
    @102
    @97
    @74
    @104
    chash
    @97
    @74
    @63
    @99
    wo
    #
    vg
    cA
    crab
    @104
    @97
    @73
    @106
    vg
    cA
    @97
    @96
    @73
    @106
    wb
    @98
    @4
    c1
    @60
    elfzp1
    syl
    rabbidv
    @63
    @99
    vg
    cA
    unrab
    syl6eqr
    fveq2d
    @64
    cfn
    wcel
    #
    @100
    cfn
    wcel
    #
    @64
    @100
    cin
    #
    c0
    wceq
    @105
    @102
    wceq
    cA
    cfn
    wcel
    #
    @64
    cA
    wss
    @107
    cA
    @25
    cfn
    subfacp1lem.a
    @27
    @25
    cfn
    wcel
    c1
    @1
    fzfi
    @23
    @5
    vf
    deranglem
    ax-mp
    eqeltri
    #
    @63
    vg
    cA
    ssrab2
    cA
    @64
    ssfi
    mp2an
    @110
    @100
    cA
    wss
    @108
    @111
    @99
    vg
    cA
    ssrab2
    cA
    @100
    ssfi
    mp2an
    @109
    @63
    @99
    wa
    #
    vg
    cA
    crab
    #
    c0
    @63
    @99
    vg
    cA
    inrab
    @113
    c0
    wceq
    @112
    wn
    #
    vg
    cA
    wral
    @114
    vg
    cA
    @62
    @70
    csn
    #
    cin
    #
    c0
    wceq
    @114
    c1
    @60
    fzp1disj
    @112
    @116
    c0
    @99
    @63
    @4
    @115
    wcel
    @116
    c0
    wne
    @4
    @70
    @83
    elsn
    @4
    @62
    @115
    inelcm
    sylan2br
    necon2bi
    ax-mp
    rgenw
    @112
    vg
    cA
    rabeq0
    mpbir
    eqtri
    @64
    @100
    hashun
    mp3an
    syl6eq
    @97
    @77
    @66
    c1
    caddc
    co
    #
    @13
    cmul
    co
    @67
    c1
    @13
    cmul
    co
    #
    caddc
    co
    @103
    @97
    @76
    @117
    @13
    cmul
    @97
    @60
    c1
    c1
    @94
    @60
    cc
    wcel
    #
    @0
    @71
    @60
    nncn
    #
    ad2antlr
    #
    c1
    cc
    wcel
    #
    @97
    ax-1cn
    a1i
    #
    @123
    addsubd
    oveq1d
    @97
    @66
    c1
    @13
    @97
    @119
    @122
    @66
    cc
    wcel
    @121
    ax-1cn
    @60
    c1
    subcl
    sylancl
    @123
    @97
    @13
    @0
    @13
    cn0
    wcel
    @94
    @71
    @93
    ad2antrr
    nn0cnd
    #
    adddird
    @97
    @118
    @101
    @67
    caddc
    @97
    @118
    @13
    @101
    @97
    @13
    @124
    mulid2d
    @97
    @101
    @99
    @70
    @3
    cfv
    #
    c1
    wne
    #
    wa
    #
    vg
    cA
    crab
    #
    chash
    cfv
    #
    @99
    @125
    c1
    wceq
    #
    wa
    #
    vg
    cA
    crab
    #
    chash
    cfv
    #
    caddc
    co
    #
    @13
    @101
    @128
    @132
    cun
    #
    chash
    cfv
    #
    @134
    @100
    @135
    chash
    @100
    @127
    @131
    wo
    #
    vg
    cA
    crab
    @135
    @99
    @137
    vg
    cA
    @99
    @99
    @126
    @130
    wo
    #
    wa
    @137
    @138
    @99
    @130
    @126
    wo
    @138
    @125
    c1
    exmidne
    @130
    @126
    orcom
    mpbi
    biantru
    @99
    @126
    @130
    andi
    bitri
    rabbii
    @127
    @131
    vg
    cA
    unrab
    eqtr4i
    fveq2i
    @128
    cfn
    wcel
    #
    @132
    cfn
    wcel
    #
    @128
    @132
    cin
    #
    c0
    wceq
    @136
    @134
    wceq
    @110
    @128
    cA
    wss
    @139
    @111
    @127
    vg
    cA
    ssrab2
    cA
    @128
    ssfi
    mp2an
    @110
    @132
    cA
    wss
    @140
    @111
    @131
    vg
    cA
    ssrab2
    cA
    @132
    ssfi
    mp2an
    @141
    @127
    @131
    wa
    #
    vg
    cA
    crab
    #
    c0
    @127
    @131
    vg
    cA
    inrab
    @143
    c0
    wceq
    @142
    wn
    #
    vg
    cA
    wral
    @144
    vg
    cA
    @127
    @131
    wn
    #
    wi
    @144
    @126
    @145
    @99
    @131
    @125
    c1
    @99
    @130
    simpr
    necon3ai
    adantl
    @127
    @131
    imnan
    mpbi
    rgenw
    @142
    vg
    cA
    rabeq0
    mpbir
    eqtri
    @128
    @132
    hashun
    mp3an
    eqtri
    @97
    @129
    @10
    @133
    @12
    caddc
    @97
    vx
    vy
    cA
    @128
    c2
    @1
    cfz
    co
    #
    @146
    @3
    wf1o
    #
    vz
    cv
    #
    @3
    cfv
    #
    @148
    wne
    #
    vz
    @146
    wral
    #
    wa
    #
    vg
    cab
    cD
    cS
    vf
    vh
    vn
    cid
    @146
    @115
    cdif
    #
    cres
    c1
    @70
    cop
    @70
    c1
    cop
    cpr
    cun
    #
    @153
    @70
    cN
    derang.d
    subfac.n
    subfacp1lem.a
    @0
    @94
    @71
    simpll
    #
    @97
    @70
    c1
    c1
    caddc
    co
    #
    @1
    cfz
    co
    #
    @146
    @97
    @70
    c1
    wceq
    #
    wn
    #
    @70
    @157
    wcel
    #
    @94
    @159
    @0
    @71
    @94
    @159
    @60
    cc0
    wne
    @60
    nnne0
    @94
    @158
    @60
    cc0
    @158
    @70
    cc0
    c1
    caddc
    co
    #
    wceq
    #
    @94
    @60
    cc0
    wceq
    #
    @161
    c1
    @70
    0p1e1
    eqeq2i
    @94
    @119
    @162
    @163
    wb
    #
    @120
    @119
    cc0
    cc
    wcel
    @122
    @164
    0cn
    ax-1cn
    @60
    cc0
    c1
    addcan2
    mp3an23
    syl
    syl5bbr
    necon3bbid
    mpbird
    ad2antlr
    @97
    @158
    @160
    @95
    @71
    @158
    @160
    wo
    #
    @95
    @35
    @71
    @165
    wb
    @0
    @35
    @94
    @36
    adantr
    @70
    c1
    @1
    elfzp12
    syl
    biimpa
    ord
    mpd
    c2
    @156
    @1
    cfz
    df-2
    oveq1i
    syl6eleqr
    #
    @60
    c1
    caddc
    ovex
    #
    @153
    eqid
    #
    @127
    c1
    vh
    cv
    #
    cfv
    #
    @70
    wceq
    #
    @70
    @169
    cfv
    #
    c1
    wne
    #
    wa
    vg
    vh
    cA
    vg
    vh
    weq
    #
    @99
    @171
    @126
    @173
    @174
    @4
    @170
    @70
    c1
    @3
    @169
    fveq1
    eqeq1d
    #
    @174
    @125
    @172
    c1
    @70
    @3
    @169
    fveq1
    #
    neeq1d
    anbi12d
    cbvrabv
    @154
    eqid
    @152
    @146
    @146
    @18
    wf1o
    #
    @22
    vy
    @146
    wral
    #
    wa
    vg
    vf
    @38
    @147
    @177
    @151
    @178
    @146
    @146
    @3
    @18
    f1oeq1
    @151
    @20
    @3
    cfv
    #
    @20
    wne
    #
    vy
    @146
    wral
    @38
    @178
    @150
    @180
    vz
    vy
    @146
    vz
    vy
    weq
    #
    @149
    @179
    @148
    @20
    @148
    @20
    @3
    fveq2
    @181
    id
    neeq12d
    #
    cbvralv
    @38
    @180
    @22
    vy
    @146
    @38
    @179
    @21
    @20
    @20
    @3
    @18
    fveq1
    neeq1d
    #
    ralbidv
    syl5bb
    anbi12d
    cbvabv
    subfacp1lem5
    @97
    vx
    vy
    cA
    @132
    @153
    @153
    @3
    wf1o
    #
    @150
    vz
    @153
    wral
    #
    wa
    #
    vg
    cab
    cD
    cS
    vf
    vh
    vn
    @153
    @70
    cN
    derang.d
    subfac.n
    subfacp1lem.a
    @155
    @166
    @167
    @168
    @131
    @171
    @172
    c1
    wceq
    #
    wa
    vg
    vh
    cA
    @174
    @99
    @171
    @130
    @187
    @175
    @174
    @125
    @172
    c1
    @176
    eqeq1d
    anbi12d
    cbvrabv
    @186
    @153
    @153
    @18
    wf1o
    #
    @22
    vy
    @153
    wral
    #
    wa
    vg
    vf
    @38
    @184
    @188
    @185
    @189
    @153
    @153
    @3
    @18
    f1oeq1
    @185
    @180
    vy
    @153
    wral
    @38
    @189
    @150
    @180
    vz
    vy
    @153
    @182
    cbvralv
    @38
    @180
    @22
    vy
    @153
    @183
    ralbidv
    syl5bb
    anbi12d
    cbvabv
    subfacp1lem3
    oveq12d
    syl5eq
    eqtr4d
    oveq2d
    3eqtrd
    eqeq12d
    syl5ibr
    ex
    a2d
    syld
    expcom
    a2d
    nnind
    mpcom
    mpd
    @0
    @9
    cN
    @13
    cmul
    @0
    cN
    cc
    wcel
    @122
    @9
    cN
    wceq
    cN
    nncn
    ax-1cn
    cN
    c1
    pncan
    sylancl
    oveq1d
    3eqtrd
end
