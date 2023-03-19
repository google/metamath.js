include "cv.mm"
include "cfv.mm"
include "cdm.mm"
include "wcel.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "ciin.mm"
include "ciun.mm"
include "cmpt.mm"
include "cli.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "cin.mm"
include "inss1.mm"
include "sseldi.mm"
include "wceq.mm"
include "wi.mm"
include "fveq2.mm"
include "dmeqd.mm"
include "eqcom.mm"
include "imbi1i.mm"
include "imbi2i.mm"
include "bitri.mm"
include "mpbi.mm"
include "cbviinv.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "iineq1d.mm"
include "cbviunv.mm"
include "eqtri.mm"
include "syl6eleq.mm"
include "eqid.mm"
include "allbutfi.mm"
include "biimpi.mm"
include "syl.mm"
include "cn.mm"
include "elin2d.mm"
include "oveq1.mm"
include "iineq2i.mm"
include "oveq2.mm"
include "adantr.mm"
include "iineq2dv.mm"
include "iuneq2d.mm"
include "eleq2d.mm"
include "eliind.mm"
include "sylib.mm"
include "jca.mm"
include "rexanuz2.mm"
include "sylibr.mm"
include "simpll.mm"
include "simpr.mm"
include "uztrn2.mm"
include "sylan.mm"
include "simprl.mm"
include "w3a.mm"
include "simp3.mm"
include "cvv.mm"
include "cmpt2.mm"
include "oveq12.mm"
include "fveq2d.mm"
include "adantl.mm"
include "fvexd.mm"
include "ovmpt2d.mm"
include "3adant3.mm"
include "eleqtrd.mm"
include "3expa.mm"
include "adantrl.mm"
include "elind.mm"
include "crn.mm"
include "cxp.mm"
include "wfn.mm"
include "csalg.mm"
include "rabexd.mm"
include "ralrimivw.mm"
include "a1d.mm"
include "imp.mm"
include "ralrimiva.mm"
include "fnmpt2.mm"
include "fnovrn.mm"
include "syl3anc.mm"
include "ovex.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "vtocl.mm"
include "syldan.mm"
include "fveq1d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "rabeqbidv.mm"
include "ineq2d.mm"
include "eqeq12d.mm"
include "rabbidv.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "elrab.mm"
include "simprd.mm"
include "eqcomd.mm"
include "eqidd.mm"
include "ex.mm"
include "syl2anc.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "cr.mm"
include "wf.mm"
include "nfv.mm"
include "feq12d.mm"
include "smff.mm"
include "chvar.mm"
include "ffvelrnd.mm"
include "adantrr.mm"
include "nnrecred.mm"
include "readdcld.mm"
include "ad2antrr.mm"
include "rpred.mm"
include "simprr.mm"
include "ltadd2dd.mm"
include "lttrd.mm"

theorem smflimlem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cS: class S
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  assume smflimlem3.z: |- Z = ( ZZ>= ` M )
  assume smflimlem3.s: |- ( ph -> S e. SAlg )
  assume smflimlem3.m: |- ( ( ph /\ m e. Z ) -> ( F ` m ) e. ( SMblFn ` S ) )
  assume smflimlem3.d: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( m e. Z |-> ( ( F ` m ) ` x ) ) e. dom ~~> }
  assume smflimlem3.a: |- ( ph -> A e. RR )
  assume smflimlem3.p: |- P = ( m e. Z , k e. NN |-> { s e. S | { x e. dom ( F ` m ) | ( ( F ` m ) ` x ) < ( A + ( 1 / k ) ) } = ( s i^i dom ( F ` m ) ) } )
  assume smflimlem3.h: |- H = ( m e. Z , k e. NN |-> ( C ` ( m P k ) ) )
  assume smflimlem3.i: |- I = |^|_ k e. NN U_ n e. Z |^|_ m e. ( ZZ>= ` n ) ( m H k )
  assume smflimlem3.c: |- ( ( ph /\ y e. ran P ) -> ( C ` y ) e. y )
  assume smflimlem3.x: |- ( ph -> X e. ( D i^i I ) )
  assume smflimlem3.k: |- ( ph -> K e. NN )
  assume smflimlem3.y: |- ( ph -> Y e. RR+ )
  assume smflimlem3.l: |- ( ph -> ( 1 / K ) < Y )

  disjoint A k
  disjoint A m
  disjoint A s
  disjoint A x
  disjoint k m
  disjoint k s
  disjoint k x
  disjoint m s
  disjoint m x
  disjoint s x
  disjoint C k
  disjoint C m
  disjoint C s
  disjoint C y
  disjoint F i
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint k n
  disjoint m n
  disjoint n x
  disjoint F s
  disjoint i s
  disjoint H i
  disjoint H k
  disjoint H m
  disjoint H n
  disjoint K i
  disjoint K k
  disjoint K m
  disjoint K s
  disjoint K x
  disjoint K y
  disjoint i y
  disjoint M m
  disjoint P k
  disjoint P m
  disjoint P s
  disjoint P y
  disjoint S k
  disjoint S m
  disjoint S s
  disjoint X i
  disjoint X k
  disjoint X m
  disjoint X x
  disjoint Z i
  disjoint Z k
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint i ph
  disjoint k ph
  disjoint m ph
  disjoint ph y
  disjoint k x
  assert |- ( ph -> E. m e. Z A. i e. ( ZZ>= ` m ) ( X e. dom ( F ` i ) /\ ( ( F ` i ) ` X ) < ( A + Y ) ) )

  proof
    wph
    cX
    vi
    cv
    #
    cF
    cfv
    #
    cdm
    #
    wcel
    #
    cX
    @1
    cfv
    #
    cA
    c1
    cK
    cdiv
    co
    #
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    vi
    vm
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vm
    cZ
    wrex
    #
    @3
    @4
    cA
    cY
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    vi
    @10
    wral
    #
    vm
    cZ
    wrex
    wph
    @3
    cX
    @0
    cK
    cH
    co
    #
    wcel
    #
    wa
    #
    vi
    @10
    wral
    #
    vm
    cZ
    wrex
    #
    @12
    wph
    @3
    vi
    @10
    wral
    vm
    cZ
    wrex
    #
    @18
    vi
    @10
    wral
    vm
    cZ
    wrex
    #
    wa
    @21
    wph
    @22
    @23
    wph
    cX
    vm
    cZ
    vi
    @10
    @2
    ciin
    #
    ciun
    #
    wcel
    #
    @22
    wph
    cX
    vn
    cZ
    vm
    vn
    cv
    #
    cuz
    cfv
    #
    @9
    cF
    cfv
    #
    cdm
    #
    ciin
    #
    ciun
    #
    @25
    wph
    cD
    @32
    cX
    cD
    vm
    cZ
    vx
    cv
    #
    @29
    cfv
    #
    cmpt
    cli
    cdm
    wcel
    #
    vx
    @32
    crab
    @32
    smflimlem3.d
    @35
    vx
    @32
    ssrab2
    eqsstri
    wph
    cD
    cI
    cin
    cD
    cX
    cD
    cI
    inss1
    smflimlem3.x
    sseldi
    sseldi
    @32
    vn
    cZ
    vi
    @28
    @2
    ciin
    #
    ciun
    @25
    vn
    cZ
    @31
    @36
    @31
    @36
    wceq
    @27
    cZ
    wcel
    #
    vm
    vi
    @28
    @30
    @2
    @0
    @9
    wceq
    #
    @2
    @30
    wceq
    #
    wi
    #
    @9
    @0
    wceq
    #
    @30
    @2
    wceq
    #
    wi
    #
    @38
    @1
    @29
    @0
    @9
    cF
    fveq2
    #
    dmeqd
    @40
    @41
    @39
    wi
    @43
    @38
    @41
    @39
    @0
    @9
    eqcom
    #
    imbi1i
    @39
    @42
    @41
    @2
    @30
    eqcom
    imbi2i
    bitri
    mpbi
    #
    cbviinv
    a1i
    iuneq2i
    vn
    vm
    cZ
    @36
    @24
    @27
    @9
    wceq
    #
    vi
    @28
    @10
    @2
    @27
    @9
    cuz
    fveq2
    #
    iineq1d
    cbviunv
    eqtri
    syl6eleq
    @26
    @22
    @25
    @2
    vi
    vm
    cM
    cX
    cZ
    smflimlem3.z
    @25
    eqid
    allbutfi
    biimpi
    syl
    wph
    cX
    vm
    cZ
    vi
    @10
    @17
    ciin
    #
    ciun
    #
    wcel
    @23
    wph
    vk
    cX
    cn
    vm
    cZ
    vi
    @10
    @0
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
    @50
    cK
    wph
    cX
    cI
    vk
    cn
    @54
    ciin
    #
    wph
    cD
    cI
    cX
    smflimlem3.x
    elin2d
    cI
    vk
    cn
    vn
    cZ
    vm
    @28
    @9
    @51
    cH
    co
    #
    ciin
    #
    ciun
    #
    ciin
    @55
    smflimlem3.i
    vk
    cn
    @58
    @54
    @58
    @54
    wceq
    @51
    cn
    wcel
    @58
    vn
    cZ
    vi
    @28
    @52
    ciin
    #
    ciun
    @54
    vn
    cZ
    @57
    @59
    @57
    @59
    wceq
    @37
    vm
    vi
    @28
    @56
    @52
    @9
    @0
    @51
    cH
    oveq1
    cbviinv
    a1i
    iuneq2i
    vn
    vm
    cZ
    @59
    @53
    @47
    vi
    @28
    @10
    @52
    @48
    iineq1d
    cbviunv
    eqtri
    a1i
    iineq2i
    eqtri
    syl6eleq
    smflimlem3.k
    @51
    cK
    wceq
    #
    @54
    @50
    cX
    @60
    vm
    cZ
    @53
    @49
    @60
    vi
    @10
    @52
    @17
    @60
    @52
    @17
    wceq
    @0
    @10
    wcel
    #
    @51
    cK
    @0
    cH
    oveq2
    adantr
    iineq2dv
    iuneq2d
    eleq2d
    eliind
    @50
    @17
    vi
    vm
    cM
    cX
    cZ
    smflimlem3.z
    @50
    eqid
    allbutfi
    sylib
    jca
    @3
    @18
    vm
    vi
    cM
    cZ
    smflimlem3.z
    rexanuz2
    sylibr
    wph
    @20
    @11
    vm
    cZ
    wph
    @9
    cZ
    wcel
    #
    wa
    #
    @19
    @8
    vi
    @10
    @63
    @61
    wa
    #
    wph
    @0
    cZ
    wcel
    #
    @19
    @8
    wi
    wph
    @62
    @61
    simpll
    #
    @63
    @62
    @61
    @65
    wph
    @62
    simpr
    cM
    @0
    @9
    cZ
    smflimlem3.z
    uztrn2
    sylan
    #
    wph
    @65
    wa
    #
    @19
    @8
    @68
    @19
    wa
    #
    @3
    @7
    @68
    @3
    @18
    simprl
    #
    @69
    @3
    @7
    @69
    cX
    @33
    @1
    cfv
    #
    @6
    clt
    wbr
    #
    vx
    @2
    crab
    #
    wcel
    @8
    @69
    cX
    @0
    cK
    cP
    co
    #
    cC
    cfv
    #
    @2
    cin
    #
    @73
    @69
    @75
    @2
    cX
    @68
    @18
    cX
    @75
    wcel
    #
    @3
    wph
    @65
    @18
    @77
    wph
    @65
    @18
    w3a
    cX
    @17
    @75
    wph
    @65
    @18
    simp3
    wph
    @65
    @17
    @75
    wceq
    @18
    @68
    vm
    vk
    @0
    cK
    cZ
    cn
    @9
    @51
    cP
    co
    #
    cC
    cfv
    #
    @75
    cH
    cvv
    cH
    vm
    vk
    cZ
    cn
    @79
    cmpt2
    wceq
    @68
    smflimlem3.h
    a1i
    @41
    @60
    wa
    #
    @79
    @75
    wceq
    @68
    @80
    @78
    @74
    cC
    @9
    @0
    @51
    cK
    cP
    oveq12
    fveq2d
    adantl
    wph
    @65
    simpr
    #
    wph
    cK
    cn
    wcel
    #
    @65
    smflimlem3.k
    adantr
    #
    @68
    @74
    cC
    fvexd
    ovmpt2d
    3adant3
    eleqtrd
    3expa
    adantrl
    @70
    elind
    @68
    @76
    @73
    wceq
    @19
    @68
    @73
    @76
    @68
    @75
    cS
    wcel
    #
    @73
    @76
    wceq
    #
    @68
    @75
    @73
    vs
    cv
    #
    @2
    cin
    #
    wceq
    #
    vs
    cS
    crab
    #
    wcel
    @84
    @85
    wa
    @68
    @75
    @74
    @89
    wph
    @65
    @74
    cP
    crn
    #
    wcel
    #
    @75
    @74
    wcel
    #
    @68
    cP
    cZ
    cn
    cxp
    wfn
    #
    @65
    @82
    @91
    wph
    @93
    @65
    wph
    @34
    cA
    c1
    @51
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
    @30
    crab
    #
    @86
    @30
    cin
    #
    wceq
    #
    vs
    cS
    crab
    #
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
    @93
    wph
    @102
    vm
    cZ
    wph
    @62
    @102
    wph
    @102
    @62
    wph
    @101
    vk
    cn
    wph
    @99
    vs
    cS
    @100
    csalg
    @100
    eqid
    smflimlem3.s
    rabexd
    ralrimivw
    a1d
    imp
    ralrimiva
    vm
    vk
    cZ
    cn
    @100
    cP
    cvv
    smflimlem3.p
    fnmpt2
    syl
    adantr
    @81
    @83
    cZ
    cn
    @0
    cK
    cP
    fnovrn
    syl3anc
    wph
    vy
    cv
    #
    @90
    wcel
    #
    wa
    #
    @103
    cC
    cfv
    #
    @103
    wcel
    #
    wi
    wph
    @91
    wa
    #
    @92
    wi
    vy
    @74
    @0
    cK
    cP
    ovex
    @103
    @74
    wceq
    #
    @105
    @108
    @107
    @92
    @109
    @104
    @91
    wph
    @103
    @74
    @90
    eleq1
    anbi2d
    @109
    @106
    @75
    @103
    @74
    @103
    @74
    cC
    fveq2
    @109
    id
    eleq12d
    imbi12d
    smflimlem3.c
    vtocl
    syldan
    @68
    vm
    vk
    @0
    cK
    cZ
    cn
    @100
    @89
    cP
    cvv
    cP
    vm
    vk
    cZ
    cn
    @100
    cmpt2
    wceq
    @68
    smflimlem3.p
    a1i
    @80
    @100
    @89
    wceq
    @68
    @80
    @99
    @88
    vs
    cS
    @80
    @97
    @73
    @98
    @87
    @80
    @96
    @72
    vx
    @30
    @2
    @41
    @42
    @60
    @46
    adantr
    @80
    @34
    @71
    @95
    @6
    clt
    @41
    @34
    @71
    wceq
    #
    @60
    @38
    @71
    @34
    wceq
    #
    wi
    #
    @41
    @110
    wi
    #
    @38
    @33
    @1
    @29
    @44
    fveq1d
    @112
    @41
    @111
    wi
    @113
    @38
    @41
    @111
    @45
    imbi1i
    @111
    @110
    @41
    @71
    @34
    eqcom
    imbi2i
    bitri
    mpbi
    adantr
    @60
    @95
    @6
    wceq
    @41
    @60
    @94
    @5
    cA
    caddc
    @51
    cK
    c1
    cdiv
    oveq2
    oveq2d
    adantl
    breq12d
    rabeqbidv
    @41
    @98
    @87
    wceq
    @60
    @41
    @30
    @2
    @86
    @46
    ineq2d
    adantr
    eqeq12d
    rabbidv
    adantl
    @81
    @83
    wph
    @89
    cvv
    wcel
    @65
    wph
    @88
    vs
    cS
    @89
    csalg
    @89
    eqid
    smflimlem3.s
    rabexd
    adantr
    ovmpt2d
    eleqtrd
    @88
    @85
    vs
    @75
    cS
    @86
    @75
    wceq
    @87
    @76
    @73
    @86
    @75
    @2
    ineq1
    eqeq2d
    elrab
    sylib
    simprd
    eqcomd
    adantr
    eleqtrd
    @72
    @7
    vx
    cX
    @2
    @33
    cX
    wceq
    #
    @71
    @4
    @6
    @6
    clt
    @33
    cX
    @1
    fveq2
    @114
    @6
    eqidd
    breq12d
    elrab
    sylib
    simprd
    jca
    ex
    syl2anc
    ralimdva
    reximdva
    mpd
    wph
    @11
    @16
    vm
    cZ
    @63
    @8
    @15
    vi
    @10
    @64
    wph
    @65
    @8
    @15
    wi
    @66
    @67
    @68
    @8
    @15
    @68
    @8
    wa
    #
    @3
    @14
    @68
    @3
    @7
    simprl
    @115
    @4
    @6
    @13
    @68
    @3
    @4
    cr
    wcel
    @7
    @68
    @3
    wa
    @2
    cr
    cX
    @1
    @68
    @2
    cr
    @1
    wf
    #
    @3
    @63
    @30
    cr
    @29
    wf
    #
    wi
    @68
    @116
    wi
    #
    vm
    vi
    @118
    vm
    nfv
    @41
    @63
    @68
    @117
    @116
    @41
    @62
    @65
    wph
    @9
    @0
    cZ
    eleq1
    anbi2d
    @41
    @30
    @2
    cr
    @29
    @1
    @9
    @0
    cF
    fveq2
    @46
    feq12d
    imbi12d
    @63
    @30
    cS
    @29
    wph
    cS
    csalg
    wcel
    @62
    smflimlem3.s
    adantr
    smflimlem3.m
    @30
    eqid
    smff
    chvar
    adantr
    @68
    @3
    simpr
    ffvelrnd
    adantrr
    wph
    @6
    cr
    wcel
    @65
    @8
    wph
    cA
    @5
    smflimlem3.a
    wph
    cK
    smflimlem3.k
    nnrecred
    #
    readdcld
    ad2antrr
    wph
    @13
    cr
    wcel
    @65
    @8
    wph
    cA
    cY
    smflimlem3.a
    wph
    cY
    smflimlem3.y
    rpred
    #
    readdcld
    ad2antrr
    @68
    @3
    @7
    simprr
    wph
    @6
    @13
    clt
    wbr
    @65
    @8
    wph
    @5
    cY
    cA
    @119
    @120
    smflimlem3.a
    smflimlem3.l
    ltadd2dd
    ad2antrr
    lttrd
    jca
    ex
    syl2anc
    ralimdva
    reximdva
    mpd
end
