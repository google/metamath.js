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
include "caddc.mm"
include "csu.mm"
include "cmin.mm"
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
include "mulcld.mm"
include "2cnd.mm"
include "rplogcld.mm"
include "rpne0d.mm"
include "divcld.mm"
include "fzfid.mm"
include "adantr.mm"
include "cn.mm"
include "elfznn.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "readdcld.mm"
include "remulcld.mm"
include "fsumcl.mm"
include "subcld.mm"
include "divdird.mm"
include "subsubd.mm"
include "subdid.mm"
include "fsumsub.mm"
include "1cnd.mm"
include "pncand.mm"
include "oveq2d.mm"
include "mulid1d.mm"
include "3eqtr3rd.mm"
include "sumeq2dv.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"
include "2re.mm"
include "rerpdivcld.mm"
include "fsumrecl.mm"
include "resubcld.mm"
include "pntrlog2bndlem4.mm"
include "nnred.mm"
include "cc0.mm"
include "cif.mm"
include "simpl.mm"
include "simpr.mm"
include "wn.mm"
include "0red.mm"
include "ifclda.mm"
include "fmpti.mm"
include "cle.mm"
include "2rp.mm"
include "rpge0d.mm"
include "divge0d.mm"
include "absge0d.mm"
include "wceq.mm"
include "rpcnd.mm"
include "cc.mm"
include "wb.mm"
include "1re.mm"
include "rpred.mm"
include "difrp.mm"
include "sylancr.mm"
include "mpbid.mm"
include "rpre.mm"
include "eleq1.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "ifbieq1d.mm"
include "ovex.mm"
include "c0ex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "iftrue.mm"
include "eqtrd.mm"
include "subdird.mm"
include "mulid2d.mm"
include "3eqtrd.mm"
include "3eqtr4d.mm"
include "subsub3d.mm"
include "npcand.mm"
include "fveq2d.mm"
include "logdifbnd.mm"
include "eqbrtrrd.mm"
include "lemuldiv2d.mm"
include "mpbird.mm"
include "lesubadd2d.mm"
include "eqbrtrd.mm"
include "syl6eqel.mm"
include "iftrued.mm"
include "log1.mm"
include "syl6eq.mm"
include "ax-1cn.mm"
include "mul01i.mm"
include "ax-mp.mm"
include "oveq1.mm"
include "1m1e0.mm"
include "0re.mm"
include "rpne0.mm"
include "necon2bi.mm"
include "iffalsed.mm"
include "0m0e0.mm"
include "eqcoms.mm"
include "nnge1d.mm"
include "logge0d.mm"
include "lep1d.mm"
include "letrd.mm"
include "wo.mm"
include "elfzle1.mm"
include "leloed.mm"
include "mpjaodan.mm"
include "lemul2ad.mm"
include "fsumle.mm"
include "lesub2dd.mm"
include "lediv1dd.mm"
include "adantrr.mm"
include "lo1le.mm"
include "rpmulcld.mm"
include "wss.mm"
include "ioossre.mm"
include "lo1const.mm"
include "crli.mm"
include "co1.mm"
include "divlogrlim.mm"
include "rlimo1.mm"
include "mp1i.mm"
include "o1lo1d.mm"
include "lo1add.mm"
include "lo1mul.mm"
include "nnrecred.mm"
include "absdivd.mm"
include "nndivred.mm"
include "absidd.mm"
include "wne.mm"
include "nnne0d.mm"
include "divdiv2d.mm"
include "div23d.mm"
include "wral.mm"
include "ad2antrr.mm"
include "breq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "lemuldivd.mm"
include "divrec2d.mm"
include "breqtrd.mm"
include "fsumdivc.mm"
include "fsummulc1.mm"
include "3brtr4d.mm"
include "harmonicubnd.mm"
include "syl2anc.mm"
include "lemul1ad.mm"
include "divassd.mm"
include "mul32d.mm"
include "dividd.mm"
include "eqtr2d.mm"
include "addcld.mm"
include "div32d.mm"
include "eqtr4d.mm"
include "mulassd.mm"
include "eqeltrrd.mm"

theorem pntrlog2bndlem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
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
  let cA: class A
  assume pntsval.1: |- S = ( a e. RR |-> sum_ i e. ( 1 ... ( |_ ` a ) ) ( ( Lam ` i ) x. ( ( log ` i ) + ( psi ` ( a / i ) ) ) ) )
  assume pntrlog2bnd.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )
  assume pntrlog2bnd.t: |- T = ( a e. RR |-> if ( a e. RR+ , ( a x. ( log ` a ) ) , 0 ) )
  assume pntrlog2bndlem5.1: |- ( ph -> B e. RR+ )
  assume pntrlog2bndlem5.2: |- ( ph -> A. y e. RR+ ( abs ` ( ( R ` y ) / y ) ) <_ B )

  disjoint a i
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint n x
  disjoint n y
  disjoint x y
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
  disjoint A a
  disjoint c i
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint i k
  disjoint i m
  disjoint A i
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint A y
  disjoint m ph
  disjoint S c
  disjoint S k
  disjoint S m
  disjoint R c
  disjoint R m
  disjoint T m
  assert |- ( ph -> ( x e. ( 1 (,) +oo ) |-> ( ( ( ( abs ` ( R ` x ) ) x. ( log ` x ) ) - ( ( 2 / ( log ` x ) ) x. sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( abs ` ( R ` ( x / n ) ) ) x. ( log ` n ) ) ) ) / x ) ) e. <_O(1) )

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
    c1
    caddc
    co
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
    @8
    @12
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
    @8
    @12
    @13
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
    cmpt
    clo1
    wph
    vx
    @0
    @23
    @28
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @18
    @21
    caddc
    co
    #
    @1
    cdiv
    co
    @23
    @28
    @30
    @18
    @21
    @1
    @30
    @5
    @17
    @30
    @3
    @4
    @30
    @3
    @30
    @2
    @30
    @2
    @30
    @1
    crp
    wcel
    #
    @2
    cr
    wcel
    @30
    @1
    c1
    @29
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
    @30
    1rp
    a1i
    @30
    c1
    @1
    @30
    1red
    #
    @34
    @30
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
    @29
    @36
    @37
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
    #
    recnd
    @30
    @4
    @30
    @1
    @40
    relogcld
    #
    recnd
    #
    mulcld
    @30
    @6
    @16
    @30
    c2
    @4
    @30
    2cnd
    #
    @44
    @30
    @4
    @30
    @1
    @34
    @38
    rplogcld
    #
    rpne0d
    #
    divcld
    #
    @30
    @8
    @15
    vn
    @30
    c1
    @7
    fzfid
    #
    @30
    @9
    @8
    wcel
    #
    wa
    #
    @15
    @51
    @12
    @14
    @51
    @11
    @51
    @11
    @51
    @10
    crp
    wcel
    #
    @11
    cr
    wcel
    @51
    @1
    @9
    @30
    @32
    @50
    @40
    adantr
    #
    @51
    @9
    @50
    @9
    cn
    wcel
    @30
    @9
    @7
    elfznn
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
    @41
    ffvelrni
    syl
    recnd
    #
    abscld
    #
    @51
    @13
    c1
    @51
    @9
    @55
    relogcld
    #
    @51
    1red
    #
    readdcld
    #
    remulcld
    #
    recnd
    #
    fsumcl
    #
    mulcld
    #
    subcld
    @30
    @6
    @20
    @48
    @30
    @8
    @12
    vn
    @49
    @51
    @12
    @58
    recnd
    #
    fsumcl
    #
    mulcld
    #
    @30
    @1
    @34
    recnd
    #
    @30
    @1
    @40
    rpne0d
    #
    divdird
    @30
    @31
    @27
    @1
    cdiv
    @30
    @5
    @17
    @21
    cmin
    co
    #
    cmin
    co
    @31
    @27
    @30
    @5
    @17
    @21
    @30
    @5
    @30
    @3
    @4
    @42
    @43
    remulcld
    #
    recnd
    @65
    @68
    subsubd
    @30
    @71
    @26
    @5
    cmin
    @30
    @6
    @16
    @20
    cmin
    co
    #
    cmul
    co
    @71
    @26
    @30
    @6
    @16
    @20
    @48
    @64
    @67
    subdid
    @30
    @73
    @25
    @6
    cmul
    @30
    @8
    @15
    @12
    cmin
    co
    #
    vn
    csu
    @73
    @25
    @30
    @8
    @15
    @12
    vn
    @49
    @63
    @66
    fsumsub
    @30
    @8
    @74
    @24
    vn
    @51
    @12
    @14
    c1
    cmin
    co
    #
    cmul
    co
    @15
    @12
    c1
    cmul
    co
    #
    cmin
    co
    @24
    @74
    @51
    @12
    @14
    c1
    @66
    @51
    @14
    @61
    recnd
    @51
    1cnd
    #
    subdid
    @51
    @75
    @13
    @12
    cmul
    @51
    @13
    c1
    @51
    @13
    @59
    recnd
    #
    @77
    pncand
    oveq2d
    @51
    @76
    @12
    @15
    cmin
    @51
    @12
    @66
    mulid1d
    oveq2d
    3eqtr3rd
    sumeq2dv
    eqtr3d
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
    @19
    @22
    cr
    @30
    @18
    @1
    @30
    @5
    @17
    @72
    @30
    @6
    @16
    @30
    c2
    @4
    c2
    cr
    wcel
    @30
    2re
    a1i
    #
    @46
    rerpdivcld
    #
    @30
    @8
    @15
    vn
    @49
    @62
    fsumrecl
    #
    remulcld
    #
    resubcld
    #
    @40
    rerpdivcld
    #
    @30
    @21
    @1
    @30
    @6
    @20
    @80
    @30
    @8
    @12
    vn
    @49
    @58
    fsumrecl
    #
    remulcld
    @40
    rerpdivcld
    #
    wph
    vx
    @0
    @5
    @6
    @8
    @12
    @9
    cT
    cfv
    #
    @9
    c1
    cmin
    co
    #
    cT
    cfv
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
    @19
    c1
    cr
    wph
    1red
    #
    vx
    @0
    @95
    cmpt
    clo1
    wcel
    wph
    vx
    cR
    cS
    cT
    vi
    vn
    va
    pntsval.1
    pntrlog2bnd.r
    pntrlog2bnd.t
    pntrlog2bndlem4
    a1i
    @30
    @94
    @1
    @30
    @5
    @93
    @72
    @30
    @6
    @92
    @80
    @30
    @8
    @91
    vn
    @49
    @51
    @12
    @90
    @58
    @51
    @87
    @89
    @51
    @9
    cr
    wcel
    #
    @87
    cr
    wcel
    @51
    @9
    @54
    nnred
    #
    cr
    cr
    @9
    cT
    va
    cr
    cr
    va
    cv
    #
    crp
    wcel
    #
    @99
    @99
    clog
    cfv
    #
    cmul
    co
    #
    cc0
    cif
    #
    cT
    pntrlog2bnd.t
    @99
    cr
    wcel
    #
    @100
    @102
    cc0
    cr
    @104
    @100
    wa
    #
    @99
    @101
    @104
    @100
    simpl
    @105
    @99
    @104
    @100
    simpr
    relogcld
    remulcld
    @104
    @100
    wn
    wa
    0red
    ifclda
    fmpti
    #
    ffvelrni
    syl
    @51
    @88
    cr
    wcel
    #
    @89
    cr
    wcel
    @51
    @9
    c1
    @98
    @60
    resubcld
    cr
    cr
    @88
    cT
    @106
    ffvelrni
    syl
    resubcld
    #
    remulcld
    #
    fsumrecl
    #
    remulcld
    #
    resubcld
    #
    @40
    rerpdivcld
    @84
    wph
    @29
    @19
    @95
    cle
    wbr
    c1
    @1
    cle
    wbr
    #
    @30
    @18
    @94
    @1
    @83
    @112
    @40
    @30
    @93
    @17
    @5
    @111
    @82
    @72
    @30
    @92
    @16
    @6
    @110
    @81
    @80
    @30
    c2
    @4
    @79
    @46
    @30
    c2
    c2
    crp
    wcel
    #
    @30
    2rp
    a1i
    rpge0d
    divge0d
    #
    @30
    @8
    @91
    @15
    vn
    @49
    @109
    @62
    @51
    @90
    @14
    @12
    @108
    @61
    @58
    @51
    @11
    @57
    absge0d
    @51
    c1
    @9
    clt
    wbr
    #
    @90
    @14
    cle
    wbr
    c1
    @9
    wceq
    #
    @51
    @116
    wa
    #
    @90
    @9
    @13
    @88
    clog
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    @119
    caddc
    co
    #
    @14
    cle
    @118
    @9
    @13
    cmul
    co
    #
    @9
    @119
    cmul
    co
    #
    @119
    cmin
    co
    #
    cmin
    co
    @123
    @124
    cmin
    co
    #
    @119
    caddc
    co
    @90
    @122
    @118
    @123
    @124
    @119
    @118
    @9
    @13
    @118
    @9
    @51
    @9
    crp
    wcel
    #
    @116
    @55
    adantr
    #
    rpcnd
    #
    @51
    @13
    cc
    wcel
    @116
    @78
    adantr
    #
    mulcld
    @118
    @9
    @119
    @129
    @118
    @119
    @118
    @88
    @118
    @116
    @88
    crp
    wcel
    #
    @51
    @116
    simpr
    @118
    c1
    cr
    wcel
    #
    @97
    @116
    @131
    wb
    1re
    @118
    @9
    @128
    rpred
    #
    c1
    @9
    difrp
    sylancr
    mpbid
    #
    relogcld
    #
    recnd
    #
    mulcld
    @136
    subsubd
    @118
    @87
    @123
    @89
    @125
    cmin
    @118
    @127
    @87
    @123
    wceq
    @128
    @127
    @87
    @127
    @123
    cc0
    cif
    #
    @123
    @127
    @97
    @87
    @137
    wceq
    @9
    rpre
    va
    @9
    @103
    @137
    cr
    cT
    @99
    @9
    wceq
    #
    @100
    @127
    @102
    @123
    cc0
    @99
    @9
    crp
    eleq1
    @138
    @99
    @9
    @101
    @13
    cmul
    @138
    id
    @99
    @9
    clog
    fveq2
    oveq12d
    ifbieq1d
    pntrlog2bnd.t
    @127
    @123
    cc0
    @9
    @13
    cmul
    ovex
    c0ex
    ifex
    fvmpt
    syl
    @127
    @123
    cc0
    iftrue
    eqtrd
    syl
    @118
    @89
    @88
    @119
    cmul
    co
    #
    @124
    c1
    @119
    cmul
    co
    #
    cmin
    co
    @125
    @118
    @131
    @89
    @139
    wceq
    @134
    @131
    @89
    @131
    @139
    cc0
    cif
    #
    @139
    @131
    @107
    @89
    @141
    wceq
    @88
    rpre
    va
    @88
    @103
    @141
    cr
    cT
    @99
    @88
    wceq
    #
    @100
    @131
    @102
    @139
    cc0
    @99
    @88
    crp
    eleq1
    @142
    @99
    @88
    @101
    @119
    cmul
    @142
    id
    @99
    @88
    clog
    fveq2
    oveq12d
    ifbieq1d
    pntrlog2bnd.t
    @131
    @139
    cc0
    @88
    @119
    cmul
    ovex
    c0ex
    ifex
    fvmpt
    syl
    @131
    @139
    cc0
    iftrue
    eqtrd
    syl
    @118
    @9
    c1
    @119
    @129
    @118
    1cnd
    #
    @136
    subdird
    @118
    @140
    @119
    @124
    cmin
    @118
    @119
    @136
    mulid2d
    oveq2d
    3eqtrd
    oveq12d
    @118
    @121
    @126
    @119
    caddc
    @118
    @9
    @13
    @119
    @129
    @130
    @136
    subdid
    oveq1d
    3eqtr4d
    @118
    @122
    @13
    cmin
    co
    #
    c1
    cle
    wbr
    @122
    @14
    cle
    wbr
    @118
    @88
    @120
    cmul
    co
    #
    @144
    c1
    cle
    @118
    @145
    @121
    c1
    @120
    cmul
    co
    #
    cmin
    co
    @121
    @120
    cmin
    co
    @144
    @118
    @9
    c1
    @120
    @129
    @143
    @118
    @120
    @118
    @13
    @119
    @118
    @9
    @128
    relogcld
    #
    @135
    resubcld
    #
    recnd
    #
    subdird
    @118
    @146
    @120
    @121
    cmin
    @118
    @120
    @149
    mulid2d
    oveq2d
    @118
    @121
    @13
    @119
    @118
    @121
    @118
    @9
    @120
    @133
    @148
    remulcld
    #
    recnd
    @130
    @136
    subsub3d
    3eqtrd
    @118
    @145
    c1
    cle
    wbr
    @120
    c1
    @88
    cdiv
    co
    #
    cle
    wbr
    @118
    @88
    c1
    caddc
    co
    #
    clog
    cfv
    #
    @119
    cmin
    co
    #
    @120
    @151
    cle
    @118
    @153
    @13
    @119
    cmin
    @118
    @152
    @9
    clog
    @118
    @9
    c1
    @129
    @143
    npcand
    fveq2d
    oveq1d
    @118
    @131
    @154
    @151
    cle
    wbr
    @134
    @88
    logdifbnd
    syl
    eqbrtrrd
    @118
    @120
    c1
    @88
    @148
    @118
    1red
    #
    @134
    lemuldiv2d
    mpbird
    eqbrtrrd
    @118
    @122
    @13
    c1
    @118
    @121
    @119
    @150
    @135
    readdcld
    @147
    @155
    lesubadd2d
    mpbid
    eqbrtrd
    @51
    @117
    wa
    @90
    cc0
    @14
    cle
    @117
    @90
    cc0
    wceq
    #
    @51
    @156
    @9
    c1
    @9
    c1
    wceq
    #
    @90
    cc0
    cc0
    cmin
    co
    cc0
    @157
    @87
    cc0
    @89
    cc0
    cmin
    @157
    @87
    c1
    cT
    cfv
    #
    cc0
    @9
    c1
    cT
    fveq2
    @132
    @158
    cc0
    wceq
    1re
    va
    c1
    @103
    cc0
    cr
    cT
    @99
    c1
    wceq
    #
    @103
    @102
    cc0
    @159
    @100
    @102
    cc0
    @159
    @99
    c1
    crp
    @159
    id
    #
    1rp
    syl6eqel
    iftrued
    @159
    @102
    c1
    cc0
    cmul
    co
    cc0
    @159
    @99
    c1
    @101
    cc0
    cmul
    @160
    @159
    @101
    c1
    clog
    cfv
    cc0
    @99
    c1
    clog
    fveq2
    log1
    syl6eq
    oveq12d
    c1
    ax-1cn
    mul01i
    syl6eq
    eqtrd
    pntrlog2bnd.t
    c0ex
    fvmpt
    ax-mp
    syl6eq
    @157
    @89
    cc0
    cT
    cfv
    #
    cc0
    @157
    @88
    cc0
    cT
    @157
    @88
    c1
    c1
    cmin
    co
    cc0
    @9
    c1
    c1
    cmin
    oveq1
    1m1e0
    syl6eq
    fveq2d
    cc0
    cr
    wcel
    @161
    cc0
    wceq
    0re
    va
    cc0
    @103
    cc0
    cr
    cT
    @99
    cc0
    wceq
    @100
    @102
    cc0
    @100
    @99
    cc0
    @99
    rpne0
    necon2bi
    iffalsed
    pntrlog2bnd.t
    c0ex
    fvmpt
    ax-mp
    syl6eq
    oveq12d
    0m0e0
    syl6eq
    eqcoms
    adantl
    @51
    cc0
    @14
    cle
    wbr
    @117
    @51
    cc0
    @13
    @14
    @51
    0red
    @59
    @61
    @51
    @9
    @98
    @51
    @9
    @54
    nnge1d
    logge0d
    @51
    @13
    @59
    lep1d
    letrd
    adantr
    eqbrtrd
    @51
    c1
    @9
    cle
    wbr
    #
    @116
    @117
    wo
    @50
    @162
    @30
    @9
    c1
    @7
    elfzle1
    adantl
    @51
    c1
    @9
    @60
    @98
    leloed
    mpbid
    mpjaodan
    lemul2ad
    fsumle
    lemul2ad
    lesub2dd
    lediv1dd
    adantrr
    lo1le
    wph
    vx
    @0
    c2
    cB
    cmul
    co
    #
    c1
    c1
    @4
    cdiv
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    @22
    c1
    cr
    @96
    wph
    vx
    @0
    @163
    @165
    cr
    wph
    @163
    cr
    wcel
    #
    @29
    wph
    @163
    wph
    c2
    cB
    @114
    wph
    2rp
    a1i
    pntrlog2bndlem5.1
    rpmulcld
    #
    rpred
    #
    adantr
    #
    @30
    c1
    @164
    @35
    @30
    c1
    @4
    @35
    @46
    rerpdivcld
    #
    readdcld
    #
    wph
    @0
    cr
    wss
    #
    @167
    vx
    @0
    @163
    cmpt
    clo1
    wcel
    c1
    cpnf
    ioossre
    #
    @169
    vx
    @0
    @163
    lo1const
    sylancr
    wph
    vx
    @0
    c1
    @164
    cr
    @35
    @171
    wph
    @173
    @132
    vx
    @0
    c1
    cmpt
    clo1
    wcel
    @174
    @96
    vx
    @0
    c1
    lo1const
    sylancr
    wph
    vx
    @0
    @164
    @171
    vx
    @0
    @164
    cmpt
    #
    cc0
    crli
    wbr
    @175
    co1
    wcel
    wph
    vx
    divlogrlim
    cc0
    @175
    rlimo1
    mp1i
    o1lo1d
    lo1add
    @30
    @163
    wph
    @163
    crp
    wcel
    @29
    @168
    adantr
    rpge0d
    lo1mul
    @30
    @163
    @165
    @170
    @172
    remulcld
    @86
    wph
    @29
    @22
    @166
    cle
    wbr
    @113
    @30
    @6
    @20
    @1
    cdiv
    co
    #
    cmul
    co
    @6
    @4
    c1
    caddc
    co
    #
    cB
    cmul
    co
    #
    cmul
    co
    #
    @22
    @166
    cle
    @30
    @176
    @178
    @6
    @30
    @20
    @1
    @85
    @40
    rerpdivcld
    #
    @30
    @177
    cB
    @30
    @4
    c1
    @43
    @35
    readdcld
    #
    @30
    cB
    wph
    cB
    crp
    wcel
    @29
    pntrlog2bndlem5.1
    adantr
    #
    rpred
    #
    remulcld
    #
    @80
    @115
    @30
    @176
    @8
    c1
    @9
    cdiv
    co
    #
    vn
    csu
    #
    cB
    cmul
    co
    #
    @178
    @180
    @30
    @186
    cB
    @30
    @8
    @185
    vn
    @49
    @51
    @9
    @54
    nnrecred
    #
    fsumrecl
    #
    @183
    remulcld
    @184
    @30
    @8
    @12
    @1
    cdiv
    co
    #
    vn
    csu
    @8
    @185
    cB
    cmul
    co
    #
    vn
    csu
    @176
    @187
    cle
    @30
    @8
    @190
    @191
    vn
    @49
    @51
    @12
    @1
    @58
    @53
    rerpdivcld
    #
    @51
    @185
    cB
    @188
    @30
    cB
    cr
    wcel
    @50
    @183
    adantr
    #
    remulcld
    @51
    @190
    cB
    @9
    cdiv
    co
    #
    @191
    cle
    @51
    @190
    @9
    cmul
    co
    #
    cB
    cle
    wbr
    @190
    @194
    cle
    wbr
    @51
    @11
    @10
    cdiv
    co
    #
    cabs
    cfv
    #
    @195
    cB
    cle
    @51
    @197
    @12
    @10
    cdiv
    co
    #
    @12
    @9
    cmul
    co
    @1
    cdiv
    co
    @195
    @51
    @197
    @12
    @10
    cabs
    cfv
    #
    cdiv
    co
    @198
    @51
    @11
    @10
    @57
    @51
    @10
    @56
    rpcnd
    @51
    @10
    @56
    rpne0d
    absdivd
    @51
    @199
    @10
    @12
    cdiv
    @51
    @10
    @51
    @1
    @9
    @30
    @33
    @50
    @34
    adantr
    @54
    nndivred
    @51
    @10
    @56
    rpge0d
    absidd
    oveq2d
    eqtrd
    @51
    @12
    @1
    @9
    @66
    @30
    @1
    cc
    wcel
    @50
    @69
    adantr
    #
    @51
    @9
    @98
    recnd
    #
    @30
    @1
    cc0
    wne
    @50
    @70
    adantr
    #
    @51
    @9
    @54
    nnne0d
    #
    divdiv2d
    @51
    @12
    @9
    @1
    @66
    @201
    @200
    @202
    div23d
    3eqtrd
    @51
    @52
    vy
    cv
    #
    cR
    cfv
    #
    @204
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
    @197
    cB
    cle
    wbr
    #
    @56
    wph
    @209
    @29
    @50
    pntrlog2bndlem5.2
    ad2antrr
    @208
    @210
    vy
    @10
    crp
    @204
    @10
    wceq
    #
    @207
    @197
    cB
    cle
    @211
    @206
    @196
    cabs
    @211
    @205
    @11
    @204
    @10
    cdiv
    @204
    @10
    cR
    fveq2
    @211
    id
    oveq12d
    fveq2d
    breq1d
    rspcv
    sylc
    eqbrtrrd
    @51
    @190
    cB
    @9
    @192
    @193
    @55
    lemuldivd
    mpbid
    @51
    cB
    @9
    @51
    cB
    @193
    recnd
    @201
    @203
    divrec2d
    breqtrd
    fsumle
    @30
    @8
    @12
    @1
    vn
    @49
    @69
    @66
    @70
    fsumdivc
    @30
    @8
    @185
    cB
    vn
    @49
    @30
    cB
    @182
    rpcnd
    #
    @51
    @185
    @188
    recnd
    fsummulc1
    3brtr4d
    @30
    @186
    @177
    cB
    @189
    @181
    @183
    @30
    cB
    @182
    rpge0d
    @30
    @33
    @113
    @186
    @177
    cle
    wbr
    @34
    @39
    @1
    vn
    harmonicubnd
    syl2anc
    lemul1ad
    letrd
    lemul2ad
    @30
    @6
    @20
    @1
    @48
    @67
    @69
    @70
    divassd
    @30
    @166
    c2
    @165
    cmul
    co
    #
    cB
    cmul
    co
    @6
    @177
    cmul
    co
    #
    cB
    cmul
    co
    @179
    @30
    c2
    cB
    @165
    @45
    @212
    @30
    @165
    @172
    recnd
    mul32d
    @30
    @213
    @214
    cB
    cmul
    @30
    @213
    c2
    @177
    @4
    cdiv
    co
    #
    cmul
    co
    @214
    @30
    @165
    @215
    c2
    cmul
    @30
    @215
    @4
    @4
    cdiv
    co
    #
    @164
    caddc
    co
    @165
    @30
    @4
    c1
    @4
    @44
    @30
    1cnd
    #
    @44
    @47
    divdird
    @30
    @216
    c1
    @164
    caddc
    @30
    @4
    @44
    @47
    dividd
    oveq1d
    eqtr2d
    oveq2d
    @30
    c2
    @4
    @177
    @45
    @44
    @30
    @4
    c1
    @44
    @217
    addcld
    #
    @47
    div32d
    eqtr4d
    oveq1d
    @30
    @6
    @177
    cB
    @48
    @218
    @212
    mulassd
    3eqtrd
    3brtr4d
    adantrr
    lo1le
    lo1add
    eqeltrrd
end
