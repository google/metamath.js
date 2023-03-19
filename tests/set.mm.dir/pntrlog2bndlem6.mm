include "c1.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "clog.mm"
include "cmul.mm"
include "c2.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfz.mm"
include "csu.mm"
include "cmin.mm"
include "caddc.mm"
include "cmpt.mm"
include "clo1.mm"
include "wcel.mm"
include "wa.mm"
include "crp.mm"
include "cr.mm"
include "elioore.mm"
include "adantl.mm"
include "1rp.mm"
include "a1i.mm"
include "1red.mm"
include "clt.mm"
include "wbr.mm"
include "eliooord.mm"
include "simpld.mm"
include "ltled.mm"
include "rpgecld.mm"
include "pntrf.mm"
include "ffvelrni.mm"
include "syl.mm"
include "recnd.mm"
include "abscld.mm"
include "relogcld.mm"
include "remulcld.mm"
include "2re.mm"
include "rplogcld.mm"
include "rerpdivcld.mm"
include "fzfid.mm"
include "adantr.mm"
include "cn.mm"
include "elfznn.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "fsumrecl.mm"
include "resubcld.mm"
include "cun.mm"
include "ssun2.mm"
include "pntrlog2bndlem6a.mm"
include "syl5sseqr.mm"
include "sselda.mm"
include "syldan.mm"
include "rpne0d.mm"
include "divdird.mm"
include "subsubd.mm"
include "subdid.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "reflcl.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "fsumsplit.mm"
include "oveq1d.mm"
include "ssun1.mm"
include "pncand.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "mpteq2dva.mm"
include "pntrlog2bndlem5.mm"
include "wss.mm"
include "ioossre.mm"
include "rpred.mm"
include "readdcld.mm"
include "cle.mm"
include "2rp.mm"
include "rpge0d.mm"
include "nnrecred.mm"
include "nndivred.mm"
include "cc.mm"
include "absge0d.mm"
include "elfzle2.mm"
include "cz.mm"
include "wb.mm"
include "nnzd.mm"
include "flge.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "logled.mm"
include "mpbid.mm"
include "lemul2ad.mm"
include "ledivmul2d.mm"
include "absdivd.mm"
include "cc0.mm"
include "divge0d.mm"
include "absidd.mm"
include "wral.mm"
include "ad2antrr.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqbrtrrd.mm"
include "letrd.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divassd.mm"
include "mulcld.mm"
include "divrecd.mm"
include "breqtrd.mm"
include "fsumle.mm"
include "fsumdivc.mm"
include "fsummulc2.mm"
include "3brtr4d.mm"
include "mulge0d.mm"
include "harmonicubnd.mm"
include "relogdivd.mm"
include "harmoniclbnd.mm"
include "le2subd.mm"
include "reccld.mm"
include "pncan2d.mm"
include "1cnd.mm"
include "pnncand.mm"
include "addcomd.mm"
include "3brtr3d.mm"
include "mulassd.mm"
include "mul12d.mm"
include "2cnd.mm"
include "div32d.mm"
include "addcld.mm"
include "ledivmuld.mm"
include "adantrr.mm"
include "ello1d.mm"
include "lo1add.mm"
include "eqeltrrd.mm"

theorem pntrlog2bndlem6
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let vi: setvar i
  let vn: setvar n
  let va: setvar a
  let vc: setvar c
  let vk: setvar k
  let vm: setvar m
  assume pntsval.1: |- S = ( a e. RR |-> sum_ i e. ( 1 ... ( |_ ` a ) ) ( ( Lam ` i ) x. ( ( log ` i ) + ( psi ` ( a / i ) ) ) ) )
  assume pntrlog2bnd.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )
  assume pntrlog2bnd.t: |- T = ( a e. RR |-> if ( a e. RR+ , ( a x. ( log ` a ) ) , 0 ) )
  assume pntrlog2bndlem5.1: |- ( ph -> B e. RR+ )
  assume pntrlog2bndlem5.2: |- ( ph -> A. y e. RR+ ( abs ` ( ( R ` y ) / y ) ) <_ B )
  assume pntrlog2bndlem6.1: |- ( ph -> A e. RR )
  assume pntrlog2bndlem6.2: |- ( ph -> 1 <_ A )

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
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint n ph
  disjoint ph x
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint R n
  disjoint R x
  disjoint R y
  disjoint T n
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
  disjoint m ph
  disjoint S c
  disjoint S k
  disjoint S m
  disjoint R c
  disjoint R m
  disjoint T m
  assert |- ( ph -> ( x e. ( 1 (,) +oo ) |-> ( ( ( ( abs ` ( R ` x ) ) x. ( log ` x ) ) - ( ( 2 / ( log ` x ) ) x. sum_ n e. ( 1 ... ( |_ ` ( x / A ) ) ) ( ( abs ` ( R ` ( x / n ) ) ) x. ( log ` n ) ) ) ) / x ) ) e. <_O(1) )

  proof
    wph
    vx
    c1
    cpnf
    cioo
    co
    #
    vx
    cv
    #
    cR
    cfv
    #
    cabs
    cfv
    #
    @1
    clog
    cfv
    #
    cmul
    co
    #
    c2
    @4
    cdiv
    co
    #
    c1
    @1
    cfl
    cfv
    #
    cfz
    co
    #
    @1
    vn
    cv
    #
    cdiv
    co
    #
    cR
    cfv
    #
    cabs
    cfv
    #
    @9
    clog
    cfv
    #
    cmul
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    cmin
    co
    #
    @1
    cdiv
    co
    #
    @6
    @1
    cA
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    @7
    cfz
    co
    #
    @14
    vn
    csu
    #
    cmul
    co
    #
    @1
    cdiv
    co
    #
    caddc
    co
    #
    cmpt
    vx
    @0
    @5
    @6
    c1
    @20
    cfz
    co
    #
    @14
    vn
    csu
    #
    cmul
    co
    #
    cmin
    co
    #
    @1
    cdiv
    co
    #
    cmpt
    clo1
    wph
    vx
    @0
    @26
    @31
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @17
    @24
    caddc
    co
    #
    @1
    cdiv
    co
    @26
    @31
    @33
    @17
    @24
    @1
    @33
    @17
    @33
    @5
    @16
    @33
    @3
    @4
    @33
    @2
    @33
    @2
    @33
    @1
    crp
    wcel
    #
    @2
    cr
    wcel
    @33
    @1
    c1
    @32
    @1
    cr
    wcel
    #
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
    @33
    1rp
    a1i
    @33
    c1
    @1
    @33
    1red
    #
    @37
    @33
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
    @32
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
    #
    rpgecld
    #
    crp
    cr
    @1
    cR
    cR
    va
    pntrlog2bnd.r
    pntrf
    #
    ffvelrni
    syl
    recnd
    abscld
    @33
    @1
    @44
    relogcld
    #
    remulcld
    #
    @33
    @6
    @15
    @33
    c2
    @4
    c2
    cr
    wcel
    #
    @33
    2re
    a1i
    #
    @33
    @1
    @37
    @42
    rplogcld
    #
    rerpdivcld
    #
    @33
    @8
    @14
    vn
    @33
    c1
    @7
    fzfid
    #
    @33
    @9
    @8
    wcel
    #
    wa
    #
    @12
    @13
    @54
    @11
    @54
    @11
    @54
    @10
    crp
    wcel
    #
    @11
    cr
    wcel
    @54
    @1
    @9
    @33
    @35
    @53
    @44
    adantr
    @54
    @9
    @53
    @9
    cn
    wcel
    #
    @33
    @9
    @7
    elfznn
    #
    adantl
    #
    nnrpd
    #
    rpdivcld
    #
    crp
    cr
    @10
    cR
    @45
    ffvelrni
    syl
    recnd
    #
    abscld
    #
    @54
    @9
    @59
    relogcld
    remulcld
    #
    fsumrecl
    #
    remulcld
    #
    resubcld
    #
    recnd
    @33
    @24
    @33
    @6
    @23
    @51
    @33
    @22
    @14
    vn
    @33
    @21
    @7
    fzfid
    #
    @33
    @9
    @22
    wcel
    #
    @53
    @14
    cr
    wcel
    #
    @33
    @22
    @8
    @9
    @33
    @27
    @22
    cun
    #
    @22
    @8
    @22
    @27
    ssun2
    wph
    vx
    vy
    cA
    cB
    cR
    cS
    cT
    vi
    va
    pntsval.1
    pntrlog2bnd.r
    pntrlog2bnd.t
    pntrlog2bndlem5.1
    pntrlog2bndlem5.2
    pntrlog2bndlem6.1
    pntrlog2bndlem6.2
    pntrlog2bndlem6a
    #
    syl5sseqr
    sselda
    #
    @63
    syldan
    #
    fsumrecl
    #
    remulcld
    #
    recnd
    #
    @33
    @1
    @37
    recnd
    #
    @33
    @1
    @44
    rpne0d
    divdird
    @33
    @34
    @30
    @1
    cdiv
    @33
    @5
    @16
    @24
    cmin
    co
    #
    cmin
    co
    @34
    @30
    @33
    @5
    @16
    @24
    @33
    @5
    @47
    recnd
    @33
    @16
    @65
    recnd
    @76
    subsubd
    @33
    @78
    @29
    @5
    cmin
    @33
    @6
    @15
    @23
    cmin
    co
    #
    cmul
    co
    @78
    @29
    @33
    @6
    @15
    @23
    @33
    @6
    @51
    recnd
    @33
    @15
    @64
    recnd
    @33
    @23
    @74
    recnd
    #
    subdid
    @33
    @79
    @28
    @6
    cmul
    @33
    @79
    @28
    @23
    caddc
    co
    #
    @23
    cmin
    co
    @28
    @33
    @15
    @81
    @23
    cmin
    @33
    @27
    @22
    @14
    @8
    vn
    @33
    @20
    @21
    clt
    wbr
    @27
    @22
    cin
    c0
    wceq
    @33
    @20
    @33
    @19
    cr
    wcel
    @20
    cr
    wcel
    @33
    @1
    cA
    @37
    wph
    cA
    crp
    wcel
    @32
    wph
    cA
    c1
    pntrlog2bndlem6.1
    @38
    wph
    1rp
    a1i
    pntrlog2bndlem6.2
    rpgecld
    #
    adantr
    #
    rerpdivcld
    @19
    reflcl
    syl
    ltp1d
    c1
    @20
    @21
    @7
    fzdisj
    syl
    #
    @71
    @52
    @54
    @14
    @63
    recnd
    #
    fsumsplit
    oveq1d
    @33
    @28
    @23
    @33
    @28
    @33
    @27
    @14
    vn
    @33
    c1
    @20
    fzfid
    #
    @33
    @9
    @27
    wcel
    #
    @53
    @69
    @33
    @27
    @8
    @9
    @33
    @70
    @27
    @8
    @27
    @22
    ssun1
    @71
    syl5sseqr
    sselda
    #
    @63
    syldan
    fsumrecl
    recnd
    @80
    pncand
    eqtrd
    oveq2d
    eqtr3d
    oveq2d
    eqtr3d
    oveq1d
    eqtr3d
    mpteq2dva
    wph
    vx
    @0
    @18
    @25
    cr
    @33
    @17
    @1
    @66
    @44
    rerpdivcld
    @33
    @24
    @1
    @75
    @44
    rerpdivcld
    #
    wph
    vx
    vy
    cB
    cR
    cS
    cT
    vi
    vn
    va
    pntsval.1
    pntrlog2bnd.r
    pntrlog2bnd.t
    pntrlog2bndlem5.1
    pntrlog2bndlem5.2
    pntrlog2bndlem5
    wph
    vx
    @0
    @25
    c1
    c2
    cB
    cA
    clog
    cfv
    #
    c1
    caddc
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    @0
    cr
    wss
    wph
    c1
    cpnf
    ioossre
    a1i
    @89
    wph
    1red
    #
    wph
    c2
    @92
    @48
    wph
    2re
    a1i
    wph
    cB
    @91
    wph
    cB
    pntrlog2bndlem5.1
    rpred
    #
    wph
    @90
    c1
    wph
    cA
    @82
    relogcld
    @94
    readdcld
    remulcld
    remulcld
    #
    wph
    @32
    @25
    @93
    cle
    wbr
    #
    c1
    @1
    cle
    wbr
    #
    @33
    @97
    @24
    @1
    @93
    cmul
    co
    #
    cle
    wbr
    @33
    c2
    @23
    @4
    cdiv
    co
    #
    cmul
    co
    c2
    @1
    @92
    cmul
    co
    #
    cmul
    co
    @24
    @99
    cle
    @33
    @100
    @101
    c2
    @33
    @23
    @4
    @74
    @50
    rerpdivcld
    #
    @33
    @1
    @92
    @37
    @33
    cB
    @91
    wph
    cB
    cr
    wcel
    #
    @32
    @95
    adantr
    #
    @33
    @90
    c1
    @33
    cA
    @83
    relogcld
    #
    @39
    readdcld
    #
    remulcld
    remulcld
    #
    @49
    @33
    c2
    c2
    crp
    wcel
    @33
    2rp
    a1i
    rpge0d
    @33
    @100
    cB
    @1
    cmul
    co
    #
    @22
    c1
    @9
    cdiv
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    @101
    @102
    @33
    @108
    @110
    @33
    cB
    @1
    @104
    @37
    remulcld
    #
    @33
    @22
    @109
    vn
    @67
    @33
    @68
    wa
    #
    @9
    @113
    @53
    @56
    @72
    @57
    syl
    #
    nnrecred
    #
    fsumrecl
    #
    remulcld
    @107
    @33
    @22
    @14
    @4
    cdiv
    co
    #
    vn
    csu
    @22
    @108
    @109
    cmul
    co
    #
    vn
    csu
    @100
    @111
    cle
    @33
    @22
    @117
    @118
    vn
    @67
    @113
    @14
    @4
    @73
    @33
    @4
    crp
    wcel
    @68
    @50
    adantr
    #
    rerpdivcld
    #
    @113
    @108
    @109
    @113
    cB
    @1
    @33
    @103
    @68
    @104
    adantr
    #
    @33
    @36
    @68
    @37
    adantr
    #
    remulcld
    @115
    remulcld
    @113
    @117
    cB
    @10
    cmul
    co
    #
    @118
    cle
    @113
    @117
    @12
    @123
    @120
    @33
    @68
    @53
    @12
    cr
    wcel
    @72
    @62
    syldan
    #
    @113
    cB
    @10
    @121
    @113
    @1
    @9
    @122
    @114
    nndivred
    #
    remulcld
    @113
    @117
    @12
    cle
    wbr
    @14
    @12
    @4
    cmul
    co
    cle
    wbr
    @113
    @13
    @4
    @12
    @113
    @9
    @33
    @68
    @53
    @9
    crp
    wcel
    @72
    @59
    syldan
    #
    relogcld
    @113
    @1
    @33
    @35
    @68
    @44
    adantr
    #
    relogcld
    @124
    @113
    @11
    @33
    @68
    @53
    @11
    cc
    wcel
    @72
    @61
    syldan
    #
    absge0d
    @113
    @9
    @1
    cle
    wbr
    #
    @13
    @4
    cle
    wbr
    @113
    @129
    @9
    @7
    cle
    wbr
    #
    @68
    @130
    @33
    @9
    @21
    @7
    elfzle2
    adantl
    @113
    @36
    @9
    cz
    wcel
    @129
    @130
    wb
    @122
    @113
    @9
    @114
    nnzd
    @1
    @9
    flge
    syl2anc
    mpbird
    @113
    @9
    @1
    @126
    @127
    logled
    mpbid
    lemul2ad
    @113
    @14
    @12
    @4
    @73
    @124
    @119
    ledivmul2d
    mpbird
    @113
    @12
    @10
    cdiv
    co
    #
    cB
    cle
    wbr
    @12
    @123
    cle
    wbr
    @113
    @11
    @10
    cdiv
    co
    #
    cabs
    cfv
    #
    @131
    cB
    cle
    @113
    @133
    @12
    @10
    cabs
    cfv
    #
    cdiv
    co
    @131
    @113
    @11
    @10
    @128
    @113
    @10
    @125
    recnd
    @113
    @10
    @33
    @68
    @53
    @55
    @72
    @60
    syldan
    #
    rpne0d
    absdivd
    @113
    @134
    @10
    @12
    cdiv
    @113
    @10
    @125
    @113
    @1
    @9
    @122
    @126
    @33
    cc0
    @1
    cle
    wbr
    @68
    @33
    @1
    @44
    rpge0d
    #
    adantr
    divge0d
    absidd
    oveq2d
    eqtrd
    @113
    @55
    vy
    cv
    #
    cR
    cfv
    #
    @137
    cdiv
    co
    #
    cabs
    cfv
    #
    cB
    cle
    wbr
    #
    vy
    crp
    wral
    #
    @133
    cB
    cle
    wbr
    #
    @135
    wph
    @142
    @32
    @68
    pntrlog2bndlem5.2
    ad2antrr
    @141
    @143
    vy
    @10
    crp
    @137
    @10
    wceq
    #
    @140
    @133
    cB
    cle
    @144
    @139
    @132
    cabs
    @144
    @138
    @11
    @137
    @10
    cdiv
    @137
    @10
    cR
    fveq2
    @144
    id
    oveq12d
    fveq2d
    breq1d
    rspcv
    sylc
    eqbrtrrd
    @113
    @12
    cB
    @10
    @124
    @121
    @135
    ledivmul2d
    mpbid
    letrd
    @113
    @108
    @9
    cdiv
    co
    @123
    @118
    @113
    cB
    @1
    @9
    @113
    cB
    @121
    recnd
    #
    @33
    @1
    cc
    wcel
    @68
    @77
    adantr
    #
    @113
    @9
    @114
    nncnd
    #
    @113
    @9
    @114
    nnne0d
    #
    divassd
    @113
    @108
    @9
    @113
    cB
    @1
    @145
    @146
    mulcld
    @147
    @148
    divrecd
    eqtr3d
    breqtrd
    fsumle
    @33
    @22
    @14
    @4
    vn
    @67
    @33
    @4
    @46
    recnd
    #
    @33
    @68
    @53
    @14
    cc
    wcel
    @72
    @85
    syldan
    @33
    @4
    @50
    rpne0d
    #
    fsumdivc
    @33
    @22
    @109
    @108
    vn
    @67
    @33
    cB
    @1
    @33
    cB
    @104
    recnd
    #
    @77
    mulcld
    @113
    @109
    @115
    recnd
    fsummulc2
    3brtr4d
    @33
    @111
    @108
    @91
    cmul
    co
    #
    @101
    cle
    @33
    @110
    @91
    @108
    @116
    @106
    @112
    @33
    cB
    @1
    @104
    @37
    @33
    cB
    wph
    cB
    crp
    wcel
    @32
    pntrlog2bndlem5.1
    adantr
    rpge0d
    @136
    mulge0d
    @33
    @8
    @109
    vn
    csu
    #
    @27
    @109
    vn
    csu
    #
    cmin
    co
    #
    @4
    c1
    caddc
    co
    #
    @4
    @90
    cmin
    co
    #
    cmin
    co
    #
    @110
    @91
    cle
    @33
    @153
    @157
    @156
    @154
    @33
    @8
    @109
    vn
    @52
    @54
    @9
    @58
    nnrecred
    #
    fsumrecl
    @33
    @4
    @90
    @46
    @105
    resubcld
    @33
    @4
    c1
    @46
    @39
    readdcld
    @33
    @27
    @109
    vn
    @86
    @33
    @87
    @53
    @109
    cr
    wcel
    @88
    @159
    syldan
    fsumrecl
    @33
    @36
    @98
    @153
    @156
    cle
    wbr
    @37
    @43
    @1
    vn
    harmonicubnd
    syl2anc
    @33
    @19
    clog
    cfv
    #
    @157
    @154
    cle
    @33
    @1
    cA
    @44
    @83
    relogdivd
    @33
    @19
    crp
    wcel
    @160
    @154
    cle
    wbr
    @33
    @1
    cA
    @44
    @83
    rpdivcld
    @19
    vn
    harmoniclbnd
    syl
    eqbrtrrd
    le2subd
    @33
    @155
    @154
    @110
    caddc
    co
    #
    @154
    cmin
    co
    @110
    @33
    @153
    @161
    @154
    cmin
    @33
    @27
    @22
    @109
    @8
    vn
    @84
    @71
    @52
    @54
    @9
    @54
    @9
    @58
    nncnd
    @54
    @9
    @58
    nnne0d
    reccld
    fsumsplit
    oveq1d
    @33
    @154
    @110
    @33
    @154
    @33
    @27
    @109
    vn
    @86
    @33
    @87
    wa
    #
    @9
    @162
    @53
    @56
    @88
    @57
    syl
    nnrecred
    fsumrecl
    recnd
    @33
    @110
    @116
    recnd
    pncan2d
    eqtrd
    @33
    @158
    c1
    @90
    caddc
    co
    @91
    @33
    @4
    c1
    @90
    @149
    @33
    1cnd
    #
    @33
    @90
    @105
    recnd
    #
    pnncand
    @33
    c1
    @90
    @163
    @164
    addcomd
    eqtrd
    3brtr3d
    lemul2ad
    @33
    @152
    cB
    @1
    @91
    cmul
    co
    cmul
    co
    @101
    @33
    cB
    @1
    @91
    @151
    @77
    @33
    @91
    @106
    recnd
    #
    mulassd
    @33
    cB
    @1
    @91
    @151
    @77
    @165
    mul12d
    eqtrd
    breqtrd
    letrd
    lemul2ad
    @33
    c2
    @4
    @23
    @33
    2cnd
    #
    @149
    @80
    @150
    div32d
    @33
    @1
    c2
    @92
    @77
    @166
    @33
    cB
    @91
    @151
    @33
    @90
    c1
    @164
    @163
    addcld
    mulcld
    mul12d
    3brtr4d
    @33
    @24
    @93
    @1
    @75
    wph
    @93
    cr
    wcel
    @32
    @96
    adantr
    @44
    ledivmuld
    mpbird
    adantrr
    ello1d
    lo1add
    eqeltrrd
end
