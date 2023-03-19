include "c1.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "caddc.mm"
include "cdiv.mm"
include "cmin.mm"
include "cabs.mm"
include "cmul.mm"
include "csu.mm"
include "clog.mm"
include "c2.mm"
include "cr.mm"
include "1red.mm"
include "wcel.mm"
include "rpred.mm"
include "adantr.mm"
include "wa.mm"
include "fzfid.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnred.mm"
include "crp.mm"
include "elioore.mm"
include "1rp.mm"
include "a1i.mm"
include "clt.mm"
include "wbr.mm"
include "eliooord.mm"
include "simpld.mm"
include "ltled.mm"
include "rpgecld.mm"
include "nnrpd.mm"
include "rpaddcld.mm"
include "rpdivcld.mm"
include "pntrf.mm"
include "ffvelrni.mm"
include "syl.mm"
include "recnd.mm"
include "subcld.mm"
include "abscld.mm"
include "remulcld.mm"
include "fsumrecl.mm"
include "rplogcld.mm"
include "rpmulcld.mm"
include "rerpdivcld.mm"
include "wss.mm"
include "cc.mm"
include "cmpt.mm"
include "co1.mm"
include "ioossre.mm"
include "rpcnd.mm"
include "o1const.mm"
include "sylancr.mm"
include "cchp.mm"
include "cle.mm"
include "wral.mm"
include "wrex.mm"
include "chpo1ubb.mm"
include "simpl.mm"
include "simpr.mm"
include "pntrlog2bndlem2.mm"
include "rexlimiva.mm"
include "mp1i.mm"
include "o1mul2.mm"
include "resubcld.mm"
include "pntsf.mm"
include "2re.mm"
include "relogcld.mm"
include "fsumabs.mm"
include "absge0d.mm"
include "abs2difabsd.mm"
include "abssubd.mm"
include "breqtrd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "2cnd.mm"
include "mulcld.mm"
include "absmuld.mm"
include "subdird.mm"
include "divcan1d.mm"
include "mul32d.mm"
include "mulassd.mm"
include "eqtr3d.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "rpge0d.mm"
include "absidd.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "cico.mm"
include "nnge1d.mm"
include "wb.mm"
include "1re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "sylanbrc.mm"
include "ad2antrr.mm"
include "weq.mm"
include "fveq2.mm"
include "id.mm"
include "breq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "lemul1ad.mm"
include "eqbrtrd.mm"
include "lemul12ad.mm"
include "mulcomd.mm"
include "3brtr4d.mm"
include "fsumle.mm"
include "fsummulc2.mm"
include "breqtrrd.mm"
include "letrd.mm"
include "lediv1dd.mm"
include "rpne0d.mm"
include "absdivd.mm"
include "eqtr2d.mm"
include "divassd.mm"
include "3brtr3d.mm"
include "leabsd.mm"
include "adantrr.mm"
include "o1le.mm"

theorem pntrlog2bndlem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vn: setvar n
  let va: setvar a
  let vc: setvar c
  let vk: setvar k
  let vm: setvar m
  let cB: class B
  let cT: class T
  assume pntsval.1: |- S = ( a e. RR |-> sum_ i e. ( 1 ... ( |_ ` a ) ) ( ( Lam ` i ) x. ( ( log ` i ) + ( psi ` ( a / i ) ) ) ) )
  assume pntrlog2bnd.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )
  assume pntrlog2bndlem3.1: |- ( ph -> A e. RR+ )
  assume pntrlog2bndlem3.2: |- ( ph -> A. y e. ( 1 [,) +oo ) ( abs ` ( ( ( S ` y ) / y ) - ( 2 x. ( log ` y ) ) ) ) <_ A )

  disjoint a i
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint A i
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint n ph
  disjoint ph x
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint R n
  disjoint R x
  disjoint R y
  disjoint a c
  disjoint a k
  disjoint a m
  disjoint c i
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint i k
  disjoint i m
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint m ph
  disjoint S c
  disjoint S k
  disjoint S m
  disjoint R c
  disjoint R m
  disjoint T m
  disjoint T n
  assert |- ( ph -> ( x e. ( 1 (,) +oo ) |-> ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( ( abs ` ( R ` ( x / n ) ) ) - ( abs ` ( R ` ( x / ( n + 1 ) ) ) ) ) x. ( ( S ` n ) - ( 2 x. ( n x. ( log ` n ) ) ) ) ) / ( x x. ( log ` x ) ) ) ) e. O(1) )

  proof
    wph
    vx
    c1
    cpnf
    cioo
    co
    #
    cA
    c1
    vx
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    #
    @1
    @4
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cR
    cfv
    #
    @1
    @4
    cdiv
    co
    #
    cR
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    vn
    csu
    #
    @1
    @1
    clog
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    @3
    @9
    cabs
    cfv
    #
    @7
    cabs
    cfv
    #
    cmin
    co
    #
    @4
    cS
    cfv
    #
    c2
    @4
    @4
    clog
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    @15
    cdiv
    co
    #
    c1
    cr
    wph
    1red
    wph
    vx
    @0
    cA
    @16
    cr
    wph
    cA
    cr
    wcel
    #
    @1
    @0
    wcel
    #
    wph
    cA
    pntrlog2bndlem3.1
    rpred
    adantr
    #
    wph
    @30
    wa
    #
    @13
    @15
    @32
    @3
    @12
    vn
    @32
    c1
    @2
    fzfid
    #
    @32
    @4
    @3
    wcel
    #
    wa
    #
    @4
    @11
    @35
    @4
    @34
    @4
    cn
    wcel
    @32
    @4
    @2
    elfznn
    adantl
    #
    nnred
    #
    @35
    @10
    @35
    @7
    @9
    @35
    @7
    @35
    @6
    crp
    wcel
    @7
    cr
    wcel
    @35
    @1
    @5
    @32
    @1
    crp
    wcel
    @34
    @32
    @1
    c1
    @30
    @1
    cr
    wcel
    wph
    @1
    c1
    cpnf
    elioore
    adantl
    #
    c1
    crp
    wcel
    #
    @32
    1rp
    a1i
    @32
    c1
    @1
    @32
    1red
    @38
    @32
    c1
    @1
    clt
    wbr
    #
    @1
    cpnf
    clt
    wbr
    #
    @30
    @40
    @41
    wa
    wph
    @1
    c1
    cpnf
    eliooord
    adantl
    simpld
    #
    ltled
    rpgecld
    #
    adantr
    #
    @35
    @4
    c1
    @35
    @4
    @36
    nnrpd
    #
    @39
    @35
    1rp
    a1i
    rpaddcld
    rpdivcld
    crp
    cr
    @6
    cR
    cR
    va
    pntrlog2bnd.r
    pntrf
    #
    ffvelrni
    syl
    recnd
    #
    @35
    @9
    @35
    @8
    crp
    wcel
    @9
    cr
    wcel
    @35
    @1
    @4
    @44
    @45
    rpdivcld
    crp
    cr
    @8
    cR
    @46
    ffvelrni
    syl
    recnd
    #
    subcld
    abscld
    #
    remulcld
    #
    fsumrecl
    #
    @32
    @1
    @14
    @43
    @32
    @1
    @38
    @42
    rplogcld
    rpmulcld
    #
    rerpdivcld
    #
    wph
    @0
    cr
    wss
    cA
    cc
    wcel
    #
    vx
    @0
    cA
    cmpt
    co1
    wcel
    c1
    cpnf
    ioossre
    wph
    cA
    pntrlog2bndlem3.1
    rpcnd
    #
    vx
    @0
    cA
    o1const
    sylancr
    vy
    cv
    #
    cchp
    cfv
    vc
    cv
    #
    @56
    cmul
    co
    cle
    wbr
    vy
    crp
    wral
    #
    vc
    crp
    wrex
    vx
    @0
    @16
    cmpt
    co1
    wcel
    #
    wph
    vy
    vc
    chpo1ubb
    @58
    @59
    vc
    crp
    @57
    crp
    wcel
    #
    @58
    wa
    vx
    vy
    @57
    cR
    cS
    vi
    vn
    va
    pntsval.1
    pntrlog2bnd.r
    @60
    @58
    simpl
    @60
    @58
    simpr
    pntrlog2bndlem2
    rexlimiva
    mp1i
    o1mul2
    @32
    cA
    @16
    @31
    @53
    remulcld
    #
    @32
    @28
    @32
    @27
    @15
    @32
    @3
    @26
    vn
    @33
    @35
    @20
    @25
    @35
    @18
    @19
    @35
    @9
    @48
    abscld
    @35
    @7
    @47
    abscld
    resubcld
    #
    @35
    @21
    @24
    @35
    @4
    cr
    wcel
    #
    @21
    cr
    wcel
    @37
    cr
    cr
    @4
    cS
    cS
    vi
    va
    pntsval.1
    pntsf
    ffvelrni
    syl
    #
    @35
    c2
    @23
    c2
    cr
    wcel
    @35
    2re
    a1i
    @35
    @4
    @22
    @37
    @35
    @4
    @45
    relogcld
    #
    remulcld
    remulcld
    resubcld
    #
    remulcld
    #
    fsumrecl
    #
    @52
    rerpdivcld
    recnd
    #
    wph
    @30
    @28
    cabs
    cfv
    #
    @17
    cabs
    cfv
    #
    cle
    wbr
    c1
    @1
    cle
    wbr
    @32
    @70
    @17
    @71
    @32
    @28
    @69
    abscld
    @61
    @32
    @17
    @32
    @17
    @61
    recnd
    abscld
    @32
    @27
    cabs
    cfv
    #
    @15
    cdiv
    co
    #
    cA
    @13
    cmul
    co
    #
    @15
    cdiv
    co
    @70
    @17
    cle
    @32
    @72
    @74
    @15
    @32
    @27
    @32
    @27
    @68
    recnd
    #
    abscld
    #
    @32
    cA
    @13
    @31
    @51
    remulcld
    #
    @52
    @32
    @72
    @3
    @26
    cabs
    cfv
    #
    vn
    csu
    #
    @74
    @76
    @32
    @3
    @78
    vn
    @33
    @35
    @26
    @35
    @26
    @67
    recnd
    #
    abscld
    #
    fsumrecl
    @77
    @32
    @3
    @26
    vn
    @33
    @80
    fsumabs
    @32
    @79
    @3
    cA
    @12
    cmul
    co
    #
    vn
    csu
    @74
    cle
    @32
    @3
    @78
    @82
    vn
    @33
    @81
    @35
    cA
    @12
    @32
    @29
    @34
    @31
    adantr
    #
    @50
    remulcld
    @35
    @20
    cabs
    cfv
    #
    @25
    cabs
    cfv
    #
    cmul
    co
    @11
    cA
    @4
    cmul
    co
    #
    cmul
    co
    #
    @78
    @82
    cle
    @35
    @84
    @11
    @85
    @86
    @35
    @20
    @35
    @20
    @62
    recnd
    #
    abscld
    @49
    @35
    @25
    @35
    @25
    @66
    recnd
    #
    abscld
    @35
    cA
    @4
    @83
    @37
    remulcld
    @35
    @20
    @88
    absge0d
    @35
    @25
    @89
    absge0d
    @35
    @84
    @9
    @7
    cmin
    co
    cabs
    cfv
    @11
    cle
    @35
    @9
    @7
    @48
    @47
    abs2difabsd
    @35
    @9
    @7
    @48
    @47
    abssubd
    breqtrd
    @35
    @85
    @21
    @4
    cdiv
    co
    #
    c2
    @22
    cmul
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @4
    cmul
    co
    #
    @86
    cle
    @35
    @92
    @4
    cmul
    co
    #
    cabs
    cfv
    @93
    @4
    cabs
    cfv
    #
    cmul
    co
    @85
    @94
    @35
    @92
    @4
    @35
    @90
    @91
    @35
    @21
    @4
    @35
    @21
    @64
    recnd
    #
    @35
    @4
    @37
    recnd
    #
    @35
    @4
    @36
    nnne0d
    #
    divcld
    #
    @35
    c2
    @22
    @35
    2cnd
    #
    @35
    @22
    @65
    recnd
    #
    mulcld
    #
    subcld
    #
    @98
    absmuld
    @35
    @95
    @25
    cabs
    @35
    @95
    @90
    @4
    cmul
    co
    #
    @91
    @4
    cmul
    co
    #
    cmin
    co
    @25
    @35
    @90
    @91
    @4
    @100
    @103
    @98
    subdird
    @35
    @105
    @21
    @106
    @24
    cmin
    @35
    @21
    @4
    @97
    @98
    @99
    divcan1d
    @35
    c2
    @4
    cmul
    co
    @22
    cmul
    co
    @106
    @24
    @35
    c2
    @4
    @22
    @101
    @98
    @102
    mul32d
    @35
    c2
    @4
    @22
    @101
    @98
    @102
    mulassd
    eqtr3d
    oveq12d
    eqtrd
    fveq2d
    @35
    @96
    @4
    @93
    cmul
    @35
    @4
    @37
    @35
    @4
    @45
    rpge0d
    #
    absidd
    oveq2d
    3eqtr3d
    @35
    @93
    cA
    @4
    @35
    @92
    @104
    abscld
    @83
    @37
    @107
    @35
    @4
    c1
    cpnf
    cico
    co
    #
    wcel
    #
    @56
    cS
    cfv
    #
    @56
    cdiv
    co
    #
    c2
    @56
    clog
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cA
    cle
    wbr
    #
    vy
    @108
    wral
    #
    @93
    cA
    cle
    wbr
    #
    @35
    @63
    c1
    @4
    cle
    wbr
    #
    @109
    @37
    @35
    @4
    @36
    nnge1d
    c1
    cr
    wcel
    @109
    @63
    @119
    wa
    wb
    1re
    c1
    @4
    elicopnf
    ax-mp
    sylanbrc
    wph
    @117
    @30
    @34
    pntrlog2bndlem3.2
    ad2antrr
    @116
    @118
    vy
    @4
    @108
    vy
    vn
    weq
    #
    @115
    @93
    cA
    cle
    @120
    @114
    @92
    cabs
    @120
    @111
    @90
    @113
    @91
    cmin
    @120
    @110
    @21
    @56
    @4
    cdiv
    @56
    @4
    cS
    fveq2
    @120
    id
    oveq12d
    @120
    @112
    @22
    c2
    cmul
    @56
    @4
    clog
    fveq2
    oveq2d
    oveq12d
    fveq2d
    breq1d
    rspcv
    sylc
    lemul1ad
    eqbrtrd
    lemul12ad
    @35
    @20
    @25
    @88
    @89
    absmuld
    @35
    @86
    @11
    cmul
    co
    @82
    @87
    @35
    cA
    @4
    @11
    wph
    @54
    @30
    @34
    @55
    ad2antrr
    #
    @98
    @35
    @11
    @49
    recnd
    #
    mulassd
    @35
    @86
    @11
    @35
    cA
    @4
    @121
    @98
    mulcld
    @122
    mulcomd
    eqtr3d
    3brtr4d
    fsumle
    @32
    @3
    @12
    cA
    vn
    @33
    wph
    @54
    @30
    @55
    adantr
    #
    @35
    @12
    @50
    recnd
    fsummulc2
    breqtrrd
    letrd
    lediv1dd
    @32
    @70
    @72
    @15
    cabs
    cfv
    #
    cdiv
    co
    @73
    @32
    @27
    @15
    @75
    @32
    @15
    @52
    rpcnd
    #
    @32
    @15
    @52
    rpne0d
    #
    absdivd
    @32
    @124
    @15
    @72
    cdiv
    @32
    @15
    @32
    @15
    @52
    rpred
    @32
    @15
    @52
    rpge0d
    absidd
    oveq2d
    eqtr2d
    @32
    cA
    @13
    @15
    @123
    @32
    @13
    @51
    recnd
    @125
    @126
    divassd
    3brtr3d
    @32
    @17
    @61
    leabsd
    letrd
    adantrr
    o1le
end
