include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cabs.mm"
include "clog.mm"
include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "nnrpd.mm"
include "pntrf.mm"
include "ffvelrni.mm"
include "syl.mm"
include "rerpdivcld.mm"
include "recnd.mm"
include "abscld.mm"
include "relogcld.mm"
include "cc0.mm"
include "c1.mm"
include "cioo.mm"
include "ioossre.mm"
include "sseldi.mm"
include "cle.mm"
include "nnred.mm"
include "nnne0d.mm"
include "absdivd.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "absidd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "caddc.mm"
include "cvma.mm"
include "cmin.mm"
include "cn.mm"
include "peano2nnd.mm"
include "vmacl.mm"
include "peano2rem.mm"
include "cchp.mm"
include "wceq.mm"
include "pntrval.mm"
include "oveq12d.mm"
include "peano2re.mm"
include "chpcl.mm"
include "sub4d.mm"
include "cn0.mm"
include "chpp1.mm"
include "oveq1d.mm"
include "pncan2d.mm"
include "cc.mm"
include "ax-1cn.mm"
include "pncan2.mm"
include "sylancl.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "breqtrd.mm"
include "wbr.mm"
include "1red.mm"
include "resubcld.mm"
include "0red.mm"
include "c2.mm"
include "2re.mm"
include "clt.mm"
include "wa.mm"
include "eliooord.mm"
include "simpld.mm"
include "elrpd.mm"
include "rerpdivcl.mm"
include "sylancr.mm"
include "a1i.mm"
include "1lt2.mm"
include "2cn.mm"
include "div1i.mm"
include "simprd.mm"
include "wb.mm"
include "0lt1.mm"
include "2pos.mm"
include "ltdiv2.mm"
include "syl222anc.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "lttrd.mm"
include "ce.mm"
include "rpefcld.mm"
include "syl5eqel.mm"
include "rpred.mm"
include "cpnf.mm"
include "cxr.mm"
include "rpxrd.mm"
include "elioopnf.mm"
include "cmul.mm"
include "reeflogd.mm"
include "breqtrrd.mm"
include "eflt.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ltled.mm"
include "1re.mm"
include "suble0.mm"
include "vmage0.mm"
include "letrd.mm"
include "readdcl.mm"
include "vmalelog.mm"
include "ceu.mm"
include "remulcld.mm"
include "epr.mm"
include "rpmulcl.mm"
include "nnge1d.mm"
include "leadd2dd.mm"
include "2timesd.mm"
include "ere.mm"
include "c3.mm"
include "egt2lt3.mm"
include "simpli.mm"
include "ltleii.mm"
include "nngt0d.mm"
include "lemul1.mm"
include "syl112anc.mm"
include "logled.mm"
include "relogmul.mm"
include "loge.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "absdifled.mm"
include "mpbir2and.mm"
include "lediv1dd.mm"
include "eqbrtrd.mm"
include "efle.mm"
include "df-e.mm"
include "3brtr4g.mm"
include "syl5eqbr.mm"
include "logleb.mm"
include "logdivlt.mm"
include "syl22anc.mm"
include "fveq2i.mm"
include "relogefd.mm"
include "syl5eq.mm"
include "cexp.mm"
include "2rp.mm"
include "rpdivcl.mm"
include "rpcnd.mm"
include "sqvald.mm"
include "wne.mm"
include "2cnd.mm"
include "rpcnne0d.mm"
include "div12.mm"
include "syl3anc.mm"
include "rpdivcld.mm"
include "2ne0.mm"
include "divcan3d.mm"
include "resqcld.mm"
include "rehalfcld.mm"
include "1rp.mm"
include "rpaddcl.mm"
include "readdcld.mm"
include "ltaddrp2d.mm"
include "efgt1p2.mm"
include "syl6breqr.mm"
include "eqbrtrrd.mm"
include "ltdiv23d.mm"

theorem pntpbnd1a
  let wph: wff ph
  let cR: class R
  let cE: class E
  let cK: class K
  let cN: class N
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vc: setvar c
  let cA: class A
  assume pntpbnd.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )
  assume pntpbnd1.e: |- ( ph -> E e. ( 0 (,) 1 ) )
  assume pntpbnd1.x: |- X = ( exp ` ( 2 / E ) )
  assume pntpbnd1.y: |- ( ph -> Y e. ( X (,) +oo ) )
  assume pntpbnd1a.1: |- ( ph -> N e. NN )
  assume pntpbnd1a.2: |- ( ph -> ( Y < N /\ N <_ ( K x. Y ) ) )
  assume pntpbnd1a.3: |- ( ph -> ( abs ` ( R ` N ) ) <_ ( abs ` ( ( R ` ( N + 1 ) ) - ( R ` N ) ) ) )

  disjoint N a
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint K i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint K j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint K k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint K m
  disjoint n x
  disjoint n y
  disjoint K n
  disjoint x y
  disjoint K x
  disjoint K y
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint c i
  disjoint c j
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint R c
  disjoint R i
  disjoint R j
  disjoint R m
  disjoint R n
  disjoint R x
  disjoint R y
  disjoint a c
  disjoint a i
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint A c
  disjoint A i
  disjoint A j
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint A y
  disjoint E n
  disjoint E y
  disjoint Y i
  disjoint Y j
  disjoint Y k
  disjoint Y m
  disjoint Y n
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( abs ` ( ( R ` N ) / N ) ) <_ E )

  proof
    wph
    cN
    cR
    cfv
    #
    cN
    cdiv
    co
    #
    cabs
    cfv
    #
    cN
    clog
    cfv
    #
    cN
    cdiv
    co
    #
    cE
    wph
    @1
    wph
    @1
    wph
    @0
    cN
    wph
    cN
    crp
    wcel
    #
    @0
    cr
    wcel
    wph
    cN
    pntpbnd1a.1
    nnrpd
    #
    crp
    cr
    cN
    cR
    cR
    va
    pntpbnd.r
    pntrf
    ffvelrni
    syl
    #
    @6
    rerpdivcld
    recnd
    abscld
    wph
    @3
    cN
    wph
    cN
    @6
    relogcld
    #
    @6
    rerpdivcld
    #
    wph
    cc0
    c1
    cioo
    co
    #
    cr
    cE
    cc0
    c1
    ioossre
    pntpbnd1.e
    sseldi
    #
    wph
    @2
    @0
    cabs
    cfv
    #
    cN
    cdiv
    co
    #
    @4
    cle
    wph
    @2
    @12
    cN
    cabs
    cfv
    #
    cdiv
    co
    @13
    wph
    @0
    cN
    wph
    @0
    @7
    recnd
    #
    wph
    cN
    wph
    cN
    pntpbnd1a.1
    nnred
    #
    recnd
    #
    wph
    cN
    pntpbnd1a.1
    nnne0d
    absdivd
    wph
    @14
    cN
    @12
    cdiv
    wph
    cN
    @16
    wph
    cN
    wph
    cN
    pntpbnd1a.1
    nnnn0d
    #
    nn0ge0d
    absidd
    oveq2d
    eqtrd
    wph
    @12
    @3
    cN
    wph
    @0
    @15
    abscld
    #
    @8
    @6
    wph
    @12
    cN
    c1
    caddc
    co
    #
    cvma
    cfv
    #
    c1
    cmin
    co
    #
    cabs
    cfv
    #
    @3
    @19
    wph
    @22
    wph
    @22
    wph
    @21
    cr
    wcel
    #
    @22
    cr
    wcel
    wph
    @20
    cn
    wcel
    #
    @24
    wph
    cN
    pntpbnd1a.1
    peano2nnd
    #
    @20
    vmacl
    syl
    #
    @21
    peano2rem
    syl
    recnd
    abscld
    @8
    wph
    @12
    @20
    cR
    cfv
    #
    @0
    cmin
    co
    #
    cabs
    cfv
    @23
    cle
    pntpbnd1a.3
    wph
    @29
    @22
    cabs
    wph
    @29
    @20
    cchp
    cfv
    #
    @20
    cmin
    co
    #
    cN
    cchp
    cfv
    #
    cN
    cmin
    co
    #
    cmin
    co
    @30
    @32
    cmin
    co
    #
    @20
    cN
    cmin
    co
    #
    cmin
    co
    @22
    wph
    @28
    @31
    @0
    @33
    cmin
    wph
    @20
    crp
    wcel
    @28
    @31
    wceq
    wph
    @20
    @26
    nnrpd
    #
    @20
    cR
    va
    pntpbnd.r
    pntrval
    syl
    wph
    @5
    @0
    @33
    wceq
    @6
    cN
    cR
    va
    pntpbnd.r
    pntrval
    syl
    oveq12d
    wph
    @30
    @20
    @32
    cN
    wph
    @30
    wph
    @20
    cr
    wcel
    #
    @30
    cr
    wcel
    wph
    cN
    cr
    wcel
    #
    @37
    @16
    cN
    peano2re
    syl
    #
    @20
    chpcl
    syl
    recnd
    wph
    @20
    @39
    recnd
    wph
    @32
    wph
    @38
    @32
    cr
    wcel
    @16
    cN
    chpcl
    syl
    recnd
    #
    @17
    sub4d
    wph
    @34
    @21
    @35
    c1
    cmin
    wph
    @34
    @32
    @21
    caddc
    co
    #
    @32
    cmin
    co
    @21
    wph
    @30
    @41
    @32
    cmin
    wph
    cN
    cn0
    wcel
    @30
    @41
    wceq
    @18
    cN
    chpp1
    syl
    oveq1d
    wph
    @32
    @21
    @40
    wph
    @21
    @27
    recnd
    pncan2d
    eqtrd
    wph
    cN
    cc
    wcel
    c1
    cc
    wcel
    @35
    c1
    wceq
    @17
    ax-1cn
    cN
    c1
    pncan2
    sylancl
    oveq12d
    3eqtrd
    fveq2d
    breqtrd
    wph
    @23
    @3
    cle
    wbr
    c1
    @3
    cmin
    co
    #
    @21
    cle
    wbr
    @21
    c1
    @3
    caddc
    co
    #
    cle
    wbr
    wph
    @42
    cc0
    @21
    wph
    c1
    @3
    wph
    1red
    #
    @8
    resubcld
    wph
    0red
    @27
    wph
    @42
    cc0
    cle
    wbr
    #
    c1
    @3
    cle
    wbr
    #
    wph
    c1
    @3
    @44
    @8
    wph
    c1
    c2
    cE
    cdiv
    co
    #
    @3
    @44
    wph
    c2
    cr
    wcel
    #
    cE
    crp
    wcel
    #
    @47
    cr
    wcel
    #
    2re
    wph
    cE
    @11
    wph
    cc0
    cE
    clt
    wbr
    #
    cE
    c1
    clt
    wbr
    #
    wph
    cE
    @10
    wcel
    @51
    @52
    wa
    pntpbnd1.e
    cE
    cc0
    c1
    eliooord
    syl
    #
    simpld
    #
    elrpd
    #
    c2
    cE
    rerpdivcl
    sylancr
    #
    @8
    wph
    c1
    c2
    @47
    @44
    @48
    wph
    2re
    a1i
    #
    @56
    c1
    c2
    clt
    wbr
    wph
    1lt2
    a1i
    wph
    c2
    c2
    c1
    cdiv
    co
    #
    @47
    clt
    c2
    2cn
    div1i
    wph
    @52
    @58
    @47
    clt
    wbr
    #
    wph
    @51
    @52
    @53
    simprd
    wph
    cE
    cr
    wcel
    @51
    c1
    cr
    wcel
    #
    cc0
    c1
    clt
    wbr
    #
    @48
    cc0
    c2
    clt
    wbr
    #
    @52
    @59
    wb
    @11
    @54
    @44
    @61
    wph
    0lt1
    a1i
    @57
    @62
    wph
    2pos
    a1i
    cE
    c1
    c2
    ltdiv2
    syl222anc
    mpbid
    syl5eqbrr
    lttrd
    #
    wph
    @47
    @3
    clt
    wbr
    #
    @47
    ce
    cfv
    #
    @3
    ce
    cfv
    #
    clt
    wbr
    #
    wph
    @65
    cN
    @66
    clt
    wph
    @65
    cX
    cN
    clt
    pntpbnd1.x
    wph
    cX
    cY
    cN
    wph
    cX
    wph
    cX
    @65
    crp
    pntpbnd1.x
    wph
    @47
    @56
    rpefcld
    syl5eqel
    #
    rpred
    #
    wph
    cY
    cr
    wcel
    #
    cX
    cY
    clt
    wbr
    #
    wph
    cY
    cX
    cpnf
    cioo
    co
    wcel
    #
    @70
    @71
    wa
    #
    pntpbnd1.y
    wph
    cX
    cxr
    wcel
    @72
    @73
    wb
    wph
    cX
    @68
    rpxrd
    cX
    cY
    elioopnf
    syl
    mpbid
    #
    simpld
    @16
    wph
    @70
    @71
    @74
    simprd
    wph
    cY
    cN
    clt
    wbr
    cN
    cK
    cY
    cmul
    co
    cle
    wbr
    pntpbnd1a.2
    simpld
    lttrd
    #
    syl5eqbrr
    wph
    cN
    @6
    reeflogd
    breqtrrd
    wph
    @50
    @3
    cr
    wcel
    #
    @64
    @67
    wb
    @56
    @8
    @47
    @3
    eflt
    syl2anc
    mpbird
    lttrd
    ltled
    #
    wph
    @60
    @76
    @45
    @46
    wb
    1re
    @8
    c1
    @3
    suble0
    sylancr
    mpbird
    wph
    @25
    cc0
    @21
    cle
    wbr
    @26
    @20
    vmage0
    syl
    letrd
    wph
    @21
    @20
    clog
    cfv
    #
    @43
    @27
    wph
    @20
    @36
    relogcld
    wph
    @60
    @76
    @43
    cr
    wcel
    1re
    @8
    c1
    @3
    readdcl
    sylancr
    wph
    @25
    @21
    @78
    cle
    wbr
    @26
    @20
    vmalelog
    syl
    wph
    @78
    ceu
    cN
    cmul
    co
    #
    clog
    cfv
    #
    @43
    cle
    wph
    @20
    @79
    cle
    wbr
    @78
    @80
    cle
    wbr
    wph
    @20
    c2
    cN
    cmul
    co
    #
    @79
    @39
    wph
    c2
    cN
    @57
    @16
    remulcld
    wph
    @79
    wph
    ceu
    crp
    wcel
    #
    @5
    @79
    crp
    wcel
    epr
    @6
    ceu
    cN
    rpmulcl
    sylancr
    #
    rpred
    wph
    @20
    cN
    cN
    caddc
    co
    @81
    cle
    wph
    c1
    cN
    cN
    @44
    @16
    @16
    wph
    cN
    pntpbnd1a.1
    nnge1d
    leadd2dd
    wph
    cN
    @17
    2timesd
    breqtrrd
    wph
    c2
    ceu
    cle
    wbr
    #
    @81
    @79
    cle
    wbr
    #
    @84
    wph
    c2
    ceu
    2re
    ere
    c2
    ceu
    clt
    wbr
    ceu
    c3
    clt
    wbr
    egt2lt3
    simpli
    ltleii
    a1i
    wph
    @48
    ceu
    cr
    wcel
    #
    @38
    cc0
    cN
    clt
    wbr
    @84
    @85
    wb
    @57
    @86
    wph
    ere
    a1i
    @16
    wph
    cN
    pntpbnd1a.1
    nngt0d
    c2
    ceu
    cN
    lemul1
    syl112anc
    mpbid
    letrd
    wph
    @20
    @79
    @36
    @83
    logled
    mpbid
    wph
    @80
    ceu
    clog
    cfv
    #
    @3
    caddc
    co
    #
    @43
    wph
    @82
    @5
    @80
    @88
    wceq
    epr
    @6
    ceu
    cN
    relogmul
    sylancr
    @87
    c1
    @3
    caddc
    loge
    oveq1i
    syl6eq
    breqtrd
    letrd
    wph
    @21
    c1
    @3
    @27
    @44
    @8
    absdifled
    mpbir2and
    letrd
    lediv1dd
    eqbrtrd
    wph
    @4
    cE
    @9
    @11
    wph
    @4
    cX
    clog
    cfv
    #
    cX
    cdiv
    co
    #
    cE
    @9
    wph
    @89
    cX
    wph
    cX
    @68
    relogcld
    @68
    rerpdivcld
    @11
    wph
    cX
    cN
    clt
    wbr
    #
    @4
    @90
    clt
    wbr
    #
    @75
    wph
    cX
    cr
    wcel
    ceu
    cX
    cle
    wbr
    @38
    ceu
    cN
    cle
    wbr
    #
    @91
    @92
    wb
    @69
    wph
    c1
    ce
    cfv
    #
    @65
    ceu
    cX
    cle
    wph
    c1
    @47
    cle
    wbr
    #
    @94
    @65
    cle
    wbr
    #
    wph
    c1
    @47
    @44
    @56
    @63
    ltled
    wph
    @60
    @50
    @95
    @96
    wb
    1re
    @56
    c1
    @47
    efle
    sylancr
    mpbid
    df-e
    pntpbnd1.x
    3brtr4g
    @16
    wph
    @93
    @87
    @3
    cle
    wbr
    #
    wph
    @87
    c1
    @3
    cle
    loge
    @77
    syl5eqbr
    wph
    @82
    @5
    @93
    @97
    wb
    epr
    @6
    ceu
    cN
    logleb
    sylancr
    mpbird
    cX
    cN
    logdivlt
    syl22anc
    mpbid
    wph
    @90
    @47
    cX
    cdiv
    co
    cE
    clt
    wph
    @89
    @47
    cX
    cdiv
    wph
    @89
    @65
    clog
    cfv
    @47
    cX
    @65
    clog
    pntpbnd1.x
    fveq2i
    wph
    @47
    @56
    relogefd
    syl5eq
    oveq1d
    wph
    @47
    cE
    cX
    @56
    @55
    @68
    wph
    @47
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    @47
    cE
    cdiv
    co
    #
    cX
    clt
    wph
    @99
    c2
    @100
    cmul
    co
    #
    c2
    cdiv
    co
    @100
    wph
    @98
    @101
    c2
    cdiv
    wph
    @98
    @47
    @47
    cmul
    co
    #
    @101
    wph
    @47
    wph
    @47
    wph
    c2
    crp
    wcel
    @49
    @47
    crp
    wcel
    #
    2rp
    @55
    c2
    cE
    rpdivcl
    sylancr
    #
    rpcnd
    #
    sqvald
    wph
    @47
    cc
    wcel
    c2
    cc
    wcel
    cE
    cc
    wcel
    cE
    cc0
    wne
    wa
    @102
    @101
    wceq
    @105
    wph
    2cnd
    #
    wph
    cE
    @55
    rpcnne0d
    @47
    c2
    cE
    div12
    syl3anc
    eqtrd
    oveq1d
    wph
    @100
    c2
    wph
    @100
    wph
    @47
    cE
    @104
    @55
    rpdivcld
    rpcnd
    @106
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    divcan3d
    eqtrd
    wph
    @99
    c1
    @47
    caddc
    co
    #
    @99
    caddc
    co
    #
    cX
    wph
    @98
    wph
    @47
    @56
    resqcld
    rehalfcld
    #
    wph
    @107
    @99
    wph
    @107
    wph
    c1
    crp
    wcel
    @103
    @107
    crp
    wcel
    1rp
    @104
    c1
    @47
    rpaddcl
    sylancr
    #
    rpred
    @109
    readdcld
    @69
    wph
    @99
    @107
    @109
    @110
    ltaddrp2d
    wph
    @108
    @65
    cX
    clt
    wph
    @103
    @108
    @65
    clt
    wbr
    @104
    @47
    efgt1p2
    syl
    pntpbnd1.x
    syl6breqr
    lttrd
    eqbrtrrd
    ltdiv23d
    eqbrtrd
    lttrd
    ltled
    letrd
end
