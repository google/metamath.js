include "cc0.mm"
include "c3.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cprime.mm"
include "cin.mm"
include "wcel.mm"
include "wn.mm"
include "cn.mm"
include "crepr.mm"
include "crab.mm"
include "ciun.mm"
include "cvma.mm"
include "c1.mm"
include "c2.mm"
include "cmul.mm"
include "csu.mm"
include "cdif.mm"
include "cle.mm"
include "cfn.mm"
include "fzofi.mm"
include "a1i.mm"
include "nnnn0d.mm"
include "cn0.mm"
include "3nn0.mm"
include "wss.mm"
include "ssid.mm"
include "reprfi2.mm"
include "ssrab2.mm"
include "ssfid.mm"
include "adantr.mm"
include "wa.mm"
include "cr.mm"
include "wf.mm"
include "vmaf.mm"
include "cz.mm"
include "nn0zd.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "sseldi.mm"
include "reprf.mm"
include "ctp.mm"
include "c0ex.mm"
include "tpid1.mm"
include "fzo0to3tp.mm"
include "eleqtrri.mm"
include "ffvelrnd.mm"
include "1ex.mm"
include "tpid2.mm"
include "2ex.mm"
include "tpid3.mm"
include "remulcld.mm"
include "wbr.mm"
include "vmage0.mm"
include "syl.mm"
include "mulge0d.mm"
include "fsumiunle.mm"
include "eqid.mm"
include "inss2.mm"
include "prmssnn.mm"
include "sstri.mm"
include "reprdifc.mm"
include "sumeq1d.mm"
include "chash.mm"
include "cc.mm"
include "wceq.mm"
include "sselda.mm"
include "fsumrecl.mm"
include "recnd.mm"
include "fsumconst.mm"
include "syl2anc.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cid.mm"
include "cres.mm"
include "cpr.mm"
include "cpmtr.mm"
include "cif.mm"
include "3nn.mm"
include "ralrimivw.mm"
include "r19.21bi.mm"
include "eleq1d.mm"
include "notbid.mm"
include "cbvrabv.mm"
include "reprpmtf1o.mm"
include "eqidd.mm"
include "adantlr.mm"
include "fsumf1o.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "cbvsumv.mm"
include "cvv.mm"
include "ovexd.mm"
include "pmtridf1o.mm"
include "hgt750lemg.mm"
include "sumeq2dv.mm"
include "3eqtrrd.mm"
include "hashfzo0.mm"
include "ax-mp.mm"
include "eqcomd.mm"
include "3eqtr4rd.mm"
include "3brtr4d.mm"

theorem hgt750lema
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cN: class N
  let cO: class O
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vi: setvar i
  let vj: setvar j
  let vu: setvar u
  let ve: setvar e
  assume hgt750leme.o: |- O = { z e. ZZ | -. 2 || z }
  assume hgt750leme.n: |- ( ph -> N e. NN )
  assume hgt750lemb.2: |- ( ph -> 2 <_ N )
  assume hgt750lemb.a: |- A = { c e. ( NN ( repr ` 3 ) N ) | -. ( c ` 0 ) e. ( O i^i Prime ) }
  assume hgt750lema.f: |- F = ( d e. { c e. ( NN ( repr ` 3 ) N ) | -. ( c ` a ) e. ( O i^i Prime ) } |-> ( d o. if ( a = 0 , ( _I |` ( 0 ..^ 3 ) ) , ( ( pmTrsp ` ( 0 ..^ 3 ) ) ` { a , 0 } ) ) ) )

  disjoint A c
  disjoint A d
  disjoint A n
  disjoint c d
  disjoint c n
  disjoint d n
  disjoint N c
  disjoint N n
  disjoint c ph
  disjoint n ph
  disjoint F n
  disjoint N a
  disjoint N d
  disjoint a c
  disjoint a d
  disjoint a n
  disjoint O a
  disjoint O c
  disjoint O d
  disjoint O n
  disjoint a ph
  disjoint d ph
  disjoint O z
  disjoint A i
  disjoint A j
  disjoint A u
  disjoint c i
  disjoint c j
  disjoint c u
  disjoint d i
  disjoint d j
  disjoint d u
  disjoint i j
  disjoint i n
  disjoint i u
  disjoint j n
  disjoint j u
  disjoint n u
  disjoint N i
  disjoint N j
  disjoint N u
  disjoint i ph
  disjoint j ph
  disjoint ph u
  disjoint F e
  disjoint e n
  disjoint N e
  disjoint a e
  disjoint c e
  disjoint d e
  disjoint O e
  disjoint e ph
  assert |- ( ph -> sum_ n e. ( ( NN ( repr ` 3 ) N ) \ ( ( O i^i Prime ) ( repr ` 3 ) N ) ) ( ( Lam ` ( n ` 0 ) ) x. ( ( Lam ` ( n ` 1 ) ) x. ( Lam ` ( n ` 2 ) ) ) ) <_ ( 3 x. sum_ n e. A ( ( Lam ` ( n ` 0 ) ) x. ( ( Lam ` ( n ` 1 ) ) x. ( Lam ` ( n ` 2 ) ) ) ) ) )

  proof
    wph
    va
    cc0
    c3
    cfzo
    co
    #
    va
    cv
    #
    vc
    cv
    #
    cfv
    #
    cO
    cprime
    cin
    #
    wcel
    #
    wn
    #
    vc
    cn
    cN
    c3
    crepr
    cfv
    #
    co
    #
    crab
    #
    ciun
    #
    cc0
    vn
    cv
    #
    cfv
    #
    cvma
    cfv
    #
    c1
    @11
    cfv
    #
    cvma
    cfv
    #
    c2
    @11
    cfv
    #
    cvma
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    vn
    csu
    @0
    @9
    @19
    vn
    csu
    #
    va
    csu
    #
    @8
    @4
    cN
    @7
    co
    cdif
    #
    @19
    vn
    csu
    c3
    cA
    @19
    vn
    csu
    #
    cmul
    co
    #
    cle
    wph
    va
    @0
    @9
    @19
    vn
    @0
    cfn
    wcel
    #
    wph
    cc0
    c3
    fzofi
    a1i
    #
    wph
    @9
    cfn
    wcel
    @1
    @0
    wcel
    #
    wph
    @8
    @9
    wph
    cn
    c3
    cN
    wph
    cN
    hgt750leme.n
    nnnn0d
    #
    c3
    cn0
    wcel
    #
    wph
    3nn0
    a1i
    #
    cn
    cn
    wss
    #
    wph
    cn
    ssid
    #
    a1i
    #
    reprfi2
    #
    @9
    @8
    wss
    wph
    @6
    vc
    @8
    ssrab2
    #
    a1i
    ssfid
    adantr
    #
    wph
    @27
    wa
    #
    @11
    @9
    wcel
    #
    wa
    #
    @13
    @18
    @39
    cn
    cr
    @12
    cvma
    cn
    cr
    cvma
    wf
    #
    @39
    vmaf
    a1i
    #
    @39
    @0
    cn
    cc0
    @11
    @39
    cn
    @11
    c3
    cN
    @31
    @39
    @32
    a1i
    wph
    cN
    cz
    wcel
    #
    @27
    @38
    wph
    cN
    @28
    nn0zd
    #
    ad2antrr
    @29
    @39
    3nn0
    a1i
    @39
    @9
    @8
    @11
    @35
    @37
    @38
    simpr
    #
    sseldi
    reprf
    #
    cc0
    @0
    wcel
    #
    @39
    cc0
    cc0
    c1
    c2
    ctp
    #
    @0
    cc0
    c1
    c2
    c0ex
    tpid1
    fzo0to3tp
    eleqtrri
    #
    a1i
    #
    ffvelrnd
    #
    ffvelrnd
    #
    @39
    @15
    @17
    @39
    cn
    cr
    @14
    cvma
    @41
    @39
    @0
    cn
    c1
    @11
    @45
    c1
    @0
    wcel
    #
    @39
    c1
    @47
    @0
    cc0
    c1
    c2
    1ex
    tpid2
    fzo0to3tp
    eleqtrri
    #
    a1i
    ffvelrnd
    #
    ffvelrnd
    #
    @39
    cn
    cr
    @16
    cvma
    @41
    @39
    @0
    cn
    c2
    @11
    @45
    c2
    @0
    wcel
    #
    @39
    c2
    @47
    @0
    cc0
    c1
    c2
    2ex
    tpid3
    fzo0to3tp
    eleqtrri
    #
    a1i
    ffvelrnd
    #
    ffvelrnd
    #
    remulcld
    #
    remulcld
    @39
    @13
    @18
    @51
    @60
    @39
    @12
    cn
    wcel
    cc0
    @13
    cle
    wbr
    @50
    @12
    vmage0
    syl
    @39
    @15
    @17
    @55
    @59
    @39
    @14
    cn
    wcel
    cc0
    @15
    cle
    wbr
    @54
    @14
    vmage0
    syl
    @39
    @16
    cn
    wcel
    cc0
    @17
    cle
    wbr
    @58
    @16
    vmage0
    syl
    mulge0d
    mulge0d
    fsumiunle
    wph
    @22
    @10
    @19
    vn
    wph
    va
    cn
    @4
    @9
    c3
    cN
    vc
    @9
    eqid
    @33
    @4
    cn
    wss
    wph
    @4
    cprime
    cn
    cO
    cprime
    inss2
    prmssnn
    sstri
    a1i
    @28
    @30
    reprdifc
    sumeq1d
    wph
    @0
    cc0
    @2
    cfv
    #
    @4
    wcel
    #
    wn
    #
    vc
    @8
    crab
    #
    @19
    vn
    csu
    #
    va
    csu
    #
    @0
    chash
    cfv
    #
    @65
    cmul
    co
    #
    @21
    @24
    wph
    @25
    @65
    cc
    wcel
    @66
    @68
    wceq
    @26
    wph
    @65
    wph
    @64
    @19
    vn
    wph
    @8
    @64
    @34
    @64
    @8
    wss
    wph
    @63
    vc
    @8
    ssrab2
    a1i
    #
    ssfid
    wph
    @11
    @64
    wcel
    #
    wa
    #
    @13
    @18
    @71
    cn
    cr
    @12
    cvma
    @40
    @71
    vmaf
    a1i
    #
    @71
    @0
    cn
    cc0
    @11
    @71
    cn
    @11
    c3
    cN
    @31
    @71
    @32
    a1i
    wph
    @42
    @70
    @43
    adantr
    @29
    @71
    3nn0
    a1i
    wph
    @64
    @8
    @11
    @69
    sselda
    reprf
    #
    @46
    @71
    @48
    a1i
    ffvelrnd
    ffvelrnd
    @71
    @15
    @17
    @71
    cn
    cr
    @14
    cvma
    @72
    @71
    @0
    cn
    c1
    @11
    @73
    @52
    @71
    @53
    a1i
    ffvelrnd
    ffvelrnd
    @71
    cn
    cr
    @16
    cvma
    @72
    @71
    @0
    cn
    c2
    @11
    @73
    @56
    @71
    @57
    a1i
    ffvelrnd
    ffvelrnd
    remulcld
    remulcld
    #
    fsumrecl
    recnd
    @0
    @65
    va
    fsumconst
    syl2anc
    wph
    @0
    @20
    @65
    va
    @37
    @65
    @9
    cc0
    ve
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cvma
    cfv
    #
    c1
    @76
    cfv
    #
    cvma
    cfv
    #
    c2
    @76
    cfv
    #
    cvma
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    ve
    csu
    #
    @9
    cc0
    @11
    cF
    cfv
    #
    cfv
    #
    cvma
    cfv
    #
    c1
    @86
    cfv
    #
    cvma
    cfv
    #
    c2
    @86
    cfv
    #
    cvma
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    @20
    @37
    @64
    @19
    @9
    @84
    vn
    ve
    cF
    @76
    @11
    @76
    wceq
    #
    @13
    @78
    @18
    @83
    cmul
    @96
    @12
    @77
    cvma
    cc0
    @11
    @76
    fveq1
    fveq2d
    @96
    @15
    @80
    @17
    @82
    cmul
    @96
    @14
    @79
    cvma
    c1
    @11
    @76
    fveq1
    fveq2d
    @96
    @16
    @81
    cvma
    c2
    @11
    @76
    fveq1
    fveq2d
    oveq12d
    oveq12d
    @36
    @37
    cn
    @4
    @9
    c3
    @1
    cc0
    wceq
    cid
    @0
    cres
    @1
    cc0
    cpr
    @0
    cpmtr
    cfv
    cfv
    cif
    #
    cF
    cN
    @64
    @1
    vd
    wph
    c3
    cn
    wcel
    #
    va
    @0
    wph
    @98
    va
    @0
    @98
    wph
    3nn
    a1i
    ralrimivw
    r19.21bi
    wph
    @42
    @27
    @43
    adantr
    @31
    @37
    @32
    a1i
    wph
    @27
    simpr
    #
    @63
    cc0
    vd
    cv
    #
    cfv
    #
    @4
    wcel
    #
    wn
    vc
    vd
    @8
    @2
    @100
    wceq
    #
    @62
    @102
    @103
    @61
    @101
    @4
    cc0
    @2
    @100
    fveq1
    eleq1d
    notbid
    cbvrabv
    @6
    @1
    @100
    cfv
    #
    @4
    wcel
    #
    wn
    vc
    vd
    @8
    @103
    @5
    @105
    @103
    @3
    @104
    @4
    @1
    @2
    @100
    fveq1
    eleq1d
    notbid
    cbvrabv
    @97
    eqid
    #
    hgt750lema.f
    reprpmtf1o
    @37
    @75
    @9
    wcel
    wa
    @76
    eqidd
    @37
    @70
    wa
    @19
    wph
    @70
    @19
    cr
    wcel
    @27
    @74
    adantlr
    recnd
    fsumf1o
    @85
    @95
    wceq
    @37
    @9
    @84
    @94
    ve
    vn
    @75
    @11
    wceq
    #
    @78
    @88
    @83
    @93
    cmul
    @107
    @77
    @87
    cvma
    @107
    cc0
    @76
    @86
    @75
    @11
    cF
    fveq2
    #
    fveq1d
    fveq2d
    @107
    @80
    @90
    @82
    @92
    cmul
    @107
    @79
    @89
    cvma
    @107
    c1
    @76
    @86
    @108
    fveq1d
    fveq2d
    @107
    @81
    @91
    cvma
    @107
    c2
    @76
    @86
    @108
    fveq1d
    fveq2d
    oveq12d
    oveq12d
    cbvsumv
    a1i
    @37
    @9
    @94
    @19
    vn
    @39
    @9
    @97
    cF
    cvma
    @11
    vd
    hgt750lema.f
    @39
    @0
    @97
    cvv
    @1
    cc0
    @39
    cc0
    c3
    cfzo
    ovexd
    @37
    @27
    @38
    @99
    adantr
    @49
    @106
    pmtridf1o
    @45
    @41
    @44
    hgt750lemg
    sumeq2dv
    3eqtrrd
    sumeq2dv
    wph
    c3
    @67
    @23
    @65
    cmul
    wph
    @67
    c3
    @67
    c3
    wceq
    #
    wph
    @29
    @109
    3nn0
    c3
    hashfzo0
    ax-mp
    a1i
    eqcomd
    wph
    cA
    @64
    @19
    vn
    cA
    @64
    wceq
    wph
    hgt750lemb.a
    a1i
    sumeq1d
    oveq12d
    3eqtr4rd
    3brtr4d
end
