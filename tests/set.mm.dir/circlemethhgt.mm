include "cn.mm"
include "c3.mm"
include "crepr.mm"
include "cfv.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "cv.mm"
include "cvma.mm"
include "cmul.mm"
include "cof.mm"
include "cs3.mm"
include "cprod.mm"
include "csu.mm"
include "c1.mm"
include "cioo.mm"
include "cvts.mm"
include "ci.mm"
include "c2.mm"
include "cpi.mm"
include "cneg.mm"
include "ce.mm"
include "citg.mm"
include "cexp.mm"
include "wcel.mm"
include "3nn.mm"
include "a1i.mm"
include "cc.mm"
include "cmap.mm"
include "chash.mm"
include "wceq.mm"
include "s3len.mm"
include "eqcomi.mm"
include "wf.mm"
include "cr.mm"
include "cvv.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "remulcld.mm"
include "recnd.mm"
include "vmaf.mm"
include "nnex.mm"
include "inidm.mm"
include "off.mm"
include "cnex.mm"
include "elmap.mm"
include "sylibr.mm"
include "s3cld.mm"
include "wrdfd.mm"
include "circlemeth.mm"
include "fveq2.mm"
include "fveq12d.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "elmapi.mm"
include "syl.mm"
include "wss.mm"
include "ssid.mm"
include "cz.mm"
include "nn0zd.mm"
include "cn0.mm"
include "3nn0.mm"
include "simpr.mm"
include "reprf.mm"
include "ffvelrnd.mm"
include "prodfzo03.mm"
include "ovex.mm"
include "s3fv0.mm"
include "mp1i.mm"
include "fveq1d.mm"
include "simpl.mm"
include "ctp.mm"
include "c0ex.mm"
include "tpid1.mm"
include "fzo0to3tp.mm"
include "eleqtrri.mm"
include "wfn.mm"
include "ffn.mm"
include "ax-mp.mm"
include "ffnd.mm"
include "eqidd.mm"
include "ofval.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "s3fv1.mm"
include "1ex.mm"
include "tpid2.mm"
include "s3fv2.mm"
include "2ex.mm"
include "tpid3.mm"
include "oveq12d.mm"
include "sumeq2dv.mm"
include "csn.mm"
include "cun.mm"
include "nfv.mm"
include "nfcv.mm"
include "cfn.mm"
include "fzofi.mm"
include "wn.mm"
include "wo.mm"
include "eqid.mm"
include "orci.mm"
include "cfz.mm"
include "wb.mm"
include "0elfz.mm"
include "elfznelfzob.mm"
include "mp2b.mm"
include "mpbir.mm"
include "ad2antrr.mm"
include "ioossre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "sselda.mm"
include "fzo0ss1.mm"
include "vtscl.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "fprodsplitsn.mm"
include "uncom.mm"
include "fzo0sn0fzo1.mm"
include "eqtr4i.mm"
include "prodeq1d.mm"
include "cpr.mm"
include "fzo13pr.mm"
include "eleq2i.mm"
include "vex.mm"
include "elpr.mm"
include "bitri.mm"
include "adantl.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "adantlr.mm"
include "prodeq2dv.mm"
include "fprodconst.mm"
include "cmin.mm"
include "cuz.mm"
include "nnuz.mm"
include "eleqtri.mm"
include "hashfzo.mm"
include "3m1e2.mm"
include "eqtri.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "sqcld.mm"
include "mulcomd.mm"
include "eqtr4d.mm"
include "3eqtr3d.mm"
include "itgeq2dv.mm"

theorem circlemethhgt
  let wph: wff ph
  let vx: setvar x
  let vn: setvar n
  let cH: class H
  let cK: class K
  let cN: class N
  let va: setvar a
  let vy: setvar y
  assume circlemethhgt.h: |- ( ph -> H : NN --> RR )
  assume circlemethhgt.k: |- ( ph -> K : NN --> RR )
  assume circlemethhgt.n: |- ( ph -> N e. NN0 )

  disjoint H n
  disjoint H x
  disjoint n x
  disjoint K n
  disjoint K x
  disjoint N n
  disjoint N x
  disjoint n ph
  disjoint ph x
  disjoint H a
  disjoint H y
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint n y
  disjoint x y
  disjoint K a
  disjoint K y
  disjoint N a
  disjoint a ph
  disjoint ph y
  assert |- ( ph -> sum_ n e. ( NN ( repr ` 3 ) N ) ( ( ( Lam ` ( n ` 0 ) ) x. ( H ` ( n ` 0 ) ) ) x. ( ( ( Lam ` ( n ` 1 ) ) x. ( K ` ( n ` 1 ) ) ) x. ( ( Lam ` ( n ` 2 ) ) x. ( K ` ( n ` 2 ) ) ) ) ) = S. ( 0 (,) 1 ) ( ( ( ( ( Lam oF x. H ) vts N ) ` x ) x. ( ( ( ( Lam oF x. K ) vts N ) ` x ) ^ 2 ) ) x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( -u N x. x ) ) ) ) _d x )

  proof
    wph
    cn
    cN
    c3
    crepr
    cfv
    co
    #
    cc0
    c3
    cfzo
    co
    #
    va
    cv
    #
    vn
    cv
    #
    cfv
    #
    @2
    cvma
    cH
    cmul
    cof
    #
    co
    #
    cvma
    cK
    @5
    co
    #
    @7
    cs3
    #
    cfv
    #
    cfv
    #
    va
    cprod
    #
    vn
    csu
    vx
    cc0
    c1
    cioo
    co
    #
    @1
    vx
    cv
    #
    @9
    cN
    cvts
    co
    #
    cfv
    #
    va
    cprod
    #
    ci
    c2
    cpi
    cmul
    co
    cmul
    co
    cN
    cneg
    @13
    cmul
    co
    cmul
    co
    ce
    cfv
    #
    cmul
    co
    #
    citg
    @0
    cc0
    @3
    cfv
    #
    cvma
    cfv
    #
    @19
    cH
    cfv
    #
    cmul
    co
    #
    c1
    @3
    cfv
    #
    cvma
    cfv
    #
    @23
    cK
    cfv
    #
    cmul
    co
    #
    c2
    @3
    cfv
    #
    cvma
    cfv
    #
    @27
    cK
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    vn
    csu
    vx
    @12
    @13
    @6
    cN
    cvts
    co
    #
    cfv
    #
    @13
    @7
    cN
    cvts
    co
    #
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    @17
    cmul
    co
    #
    citg
    wph
    vx
    c3
    @8
    cN
    va
    vn
    circlemethhgt.n
    c3
    cn
    wcel
    #
    wph
    3nn
    a1i
    wph
    cc
    cn
    cmap
    co
    #
    c3
    @8
    c3
    @8
    chash
    cfv
    #
    wceq
    wph
    @42
    c3
    @6
    @7
    @7
    s3len
    eqcomi
    a1i
    wph
    @6
    @7
    @7
    @41
    wph
    cn
    cc
    @6
    wf
    #
    @6
    @41
    wcel
    wph
    vx
    vy
    cn
    cn
    cn
    cmul
    cr
    cr
    cc
    cvma
    cH
    cvv
    cvv
    wph
    @13
    cr
    wcel
    #
    vy
    cv
    #
    cr
    wcel
    #
    wa
    wa
    #
    @13
    @45
    cmul
    co
    @47
    @13
    @45
    wph
    @44
    @46
    simprl
    wph
    @44
    @46
    simprr
    remulcld
    recnd
    #
    cn
    cr
    cvma
    wf
    #
    wph
    vmaf
    a1i
    #
    circlemethhgt.h
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    #
    @51
    cn
    inidm
    #
    off
    #
    cc
    cn
    @6
    cnex
    nnex
    elmap
    sylibr
    wph
    cn
    cc
    @7
    wf
    #
    @7
    @41
    wcel
    wph
    vx
    vy
    cn
    cn
    cn
    cmul
    cr
    cr
    cc
    cvma
    cK
    cvv
    cvv
    @48
    @50
    circlemethhgt.k
    @51
    @51
    @52
    off
    #
    cc
    cn
    @7
    cnex
    nnex
    elmap
    sylibr
    #
    @56
    s3cld
    wrdfd
    #
    circlemeth
    wph
    @0
    @11
    @32
    vn
    wph
    @3
    @0
    wcel
    #
    wa
    #
    @11
    @19
    cc0
    @8
    cfv
    #
    cfv
    #
    @23
    c1
    @8
    cfv
    #
    cfv
    #
    @27
    c2
    @8
    cfv
    #
    cfv
    #
    cmul
    co
    #
    cmul
    co
    @32
    @59
    @61
    @63
    @65
    @10
    va
    @2
    cc0
    wceq
    #
    @4
    @19
    @9
    @60
    @2
    cc0
    @8
    fveq2
    #
    @2
    cc0
    @3
    fveq2
    fveq12d
    @2
    c1
    wceq
    #
    @4
    @23
    @9
    @62
    @2
    c1
    @8
    fveq2
    #
    @2
    c1
    @3
    fveq2
    fveq12d
    @2
    c2
    wceq
    #
    @4
    @27
    @9
    @64
    @2
    c2
    @8
    fveq2
    #
    @2
    c2
    @3
    fveq2
    fveq12d
    @59
    @2
    @1
    wcel
    wa
    #
    cn
    cc
    @4
    @9
    @73
    @9
    @41
    wcel
    #
    cn
    cc
    @9
    wf
    #
    @59
    @1
    @41
    @2
    @8
    wph
    @1
    @41
    @8
    wf
    #
    @58
    @57
    adantr
    ffvelrnda
    @9
    cc
    cn
    elmapi
    #
    syl
    @59
    @1
    cn
    @2
    @3
    @59
    cn
    @3
    c3
    cN
    cn
    cn
    wss
    @59
    cn
    ssid
    a1i
    wph
    cN
    cz
    wcel
    @58
    wph
    cN
    circlemethhgt.n
    nn0zd
    adantr
    c3
    cn0
    wcel
    #
    @59
    3nn0
    a1i
    wph
    @58
    simpr
    reprf
    #
    ffvelrnda
    ffvelrnd
    prodfzo03
    @59
    @61
    @22
    @66
    @31
    cmul
    @59
    @61
    @19
    @6
    cfv
    #
    @22
    @59
    @19
    @60
    @6
    @6
    cvv
    wcel
    #
    @60
    @6
    wceq
    #
    @59
    cvma
    cH
    @5
    ovex
    #
    @6
    @7
    @7
    cvv
    s3fv0
    #
    mp1i
    fveq1d
    @59
    wph
    @19
    cn
    wcel
    #
    @80
    @22
    wceq
    wph
    @58
    simpl
    #
    @59
    @1
    cn
    cc0
    @3
    @79
    cc0
    @1
    wcel
    @59
    cc0
    cc0
    c1
    c2
    ctp
    #
    @1
    cc0
    c1
    c2
    c0ex
    tpid1
    fzo0to3tp
    eleqtrri
    a1i
    ffvelrnd
    wph
    cn
    cn
    @20
    @21
    cmul
    cn
    cvma
    cH
    cvv
    cvv
    @19
    cvma
    cn
    wfn
    #
    wph
    @49
    @88
    vmaf
    cn
    cr
    cvma
    ffn
    ax-mp
    a1i
    #
    wph
    cn
    cr
    cH
    circlemethhgt.h
    ffnd
    @51
    @51
    @52
    wph
    @85
    wa
    #
    @20
    eqidd
    @90
    @21
    eqidd
    ofval
    syl2anc
    eqtrd
    @59
    @63
    @26
    @65
    @30
    cmul
    @59
    @63
    @23
    @7
    cfv
    #
    @26
    @59
    @23
    @62
    @7
    @7
    cvv
    wcel
    #
    @62
    @7
    wceq
    #
    @59
    cvma
    cK
    @5
    ovex
    #
    @6
    @7
    @7
    cvv
    s3fv1
    #
    mp1i
    fveq1d
    @59
    wph
    @23
    cn
    wcel
    #
    @91
    @26
    wceq
    @86
    @59
    @1
    cn
    c1
    @3
    @79
    c1
    @1
    wcel
    @59
    c1
    @87
    @1
    cc0
    c1
    c2
    1ex
    tpid2
    fzo0to3tp
    eleqtrri
    a1i
    ffvelrnd
    wph
    cn
    cn
    @24
    @25
    cmul
    cn
    cvma
    cK
    cvv
    cvv
    @23
    @89
    wph
    cn
    cr
    cK
    circlemethhgt.k
    ffnd
    #
    @51
    @51
    @52
    wph
    @96
    wa
    #
    @24
    eqidd
    @98
    @25
    eqidd
    ofval
    syl2anc
    eqtrd
    @59
    @65
    @27
    @7
    cfv
    #
    @30
    @59
    @27
    @64
    @7
    @92
    @64
    @7
    wceq
    #
    @59
    @94
    @6
    @7
    @7
    cvv
    s3fv2
    #
    mp1i
    fveq1d
    @59
    wph
    @27
    cn
    wcel
    #
    @99
    @30
    wceq
    @86
    @59
    @1
    cn
    c2
    @3
    @79
    c2
    @1
    wcel
    @59
    c2
    @87
    @1
    cc0
    c1
    c2
    2ex
    tpid3
    fzo0to3tp
    eleqtrri
    a1i
    ffvelrnd
    wph
    cn
    cn
    @28
    @29
    cmul
    cn
    cvma
    cK
    cvv
    cvv
    @27
    @89
    @97
    @51
    @51
    @52
    wph
    @102
    wa
    #
    @28
    eqidd
    @103
    @29
    eqidd
    ofval
    syl2anc
    eqtrd
    oveq12d
    oveq12d
    eqtrd
    sumeq2dv
    wph
    vx
    @12
    @18
    @39
    wph
    @13
    @12
    wcel
    #
    wa
    #
    @16
    @38
    @17
    cmul
    @105
    c1
    c3
    cfzo
    co
    #
    cc0
    csn
    #
    cun
    #
    @15
    va
    cprod
    @106
    @15
    va
    cprod
    #
    @34
    cmul
    co
    #
    @16
    @38
    @105
    @106
    cc0
    @15
    @34
    va
    cvv
    @105
    va
    nfv
    va
    @34
    nfcv
    @106
    cfn
    wcel
    #
    @105
    c1
    c3
    fzofi
    a1i
    #
    cc0
    cvv
    wcel
    @105
    c0ex
    a1i
    cc0
    @106
    wcel
    wn
    #
    @105
    @113
    cc0
    cc0
    wceq
    #
    cc0
    c3
    wceq
    #
    wo
    #
    @114
    @115
    cc0
    eqid
    orci
    @78
    cc0
    cc0
    c3
    cfz
    co
    wcel
    @113
    @116
    wb
    3nn0
    c3
    0elfz
    c3
    cc0
    elfznelfzob
    mp2b
    mpbir
    a1i
    @105
    @2
    @106
    wcel
    #
    wa
    #
    @9
    cN
    @13
    wph
    cN
    cn0
    wcel
    #
    @104
    @117
    circlemethhgt.n
    ad2antrr
    @105
    @13
    cc
    wcel
    @117
    wph
    @12
    cc
    @13
    @12
    cc
    wss
    wph
    @12
    cr
    cc
    cc0
    c1
    ioossre
    ax-resscn
    sstri
    a1i
    sselda
    #
    adantr
    @118
    @74
    @75
    @118
    @1
    @41
    @2
    @8
    wph
    @76
    @104
    @117
    @57
    ad2antrr
    @105
    @106
    @1
    @2
    @106
    @1
    wss
    @105
    c3
    fzo0ss1
    a1i
    sselda
    ffvelrnd
    @77
    syl
    vtscl
    @67
    @13
    @14
    @33
    @67
    @9
    @6
    cN
    cvts
    @67
    @9
    @60
    @6
    @68
    @81
    @82
    @83
    @84
    ax-mp
    syl6eq
    oveq1d
    fveq1d
    @105
    @6
    cN
    @13
    wph
    @119
    @104
    circlemethhgt.n
    adantr
    #
    @120
    wph
    @43
    @104
    @53
    adantr
    vtscl
    #
    fprodsplitsn
    @105
    @108
    @1
    @15
    va
    @108
    @1
    wceq
    @105
    @108
    @107
    @106
    cun
    #
    @1
    @106
    @107
    uncom
    @40
    @1
    @123
    wceq
    3nn
    c3
    fzo0sn0fzo1
    ax-mp
    eqtr4i
    a1i
    prodeq1d
    @105
    @110
    @37
    @34
    cmul
    co
    @38
    @105
    @109
    @37
    @34
    cmul
    @105
    @109
    @106
    @36
    va
    cprod
    #
    @36
    @106
    chash
    cfv
    #
    cexp
    co
    #
    @37
    @105
    @106
    @15
    @36
    va
    @118
    @13
    @14
    @35
    @118
    @9
    @7
    cN
    cvts
    wph
    @117
    @9
    @7
    wceq
    #
    @104
    @117
    wph
    @69
    @71
    wo
    #
    @127
    @117
    @2
    c1
    c2
    cpr
    #
    wcel
    @128
    @106
    @129
    @2
    fzo13pr
    eleq2i
    @2
    c1
    c2
    va
    vex
    elpr
    bitri
    wph
    @69
    @127
    @71
    wph
    @69
    wa
    #
    @9
    @62
    @7
    @69
    @9
    @62
    wceq
    wph
    @70
    adantl
    @92
    @93
    @130
    @94
    @95
    mp1i
    eqtrd
    wph
    @71
    wa
    #
    @9
    @64
    @7
    @71
    @9
    @64
    wceq
    wph
    @72
    adantl
    @92
    @100
    @131
    @94
    @101
    mp1i
    eqtrd
    jaodan
    sylan2b
    adantlr
    oveq1d
    fveq1d
    prodeq2dv
    @105
    @111
    @36
    cc
    wcel
    @124
    @126
    wceq
    @112
    @105
    @7
    cN
    @13
    @121
    @120
    wph
    @54
    @104
    @55
    adantr
    vtscl
    #
    @106
    @36
    va
    fprodconst
    syl2anc
    @105
    @125
    c2
    @36
    cexp
    @125
    c2
    wceq
    @105
    @125
    c3
    c1
    cmin
    co
    #
    c2
    c3
    c1
    cuz
    cfv
    #
    wcel
    @125
    @133
    wceq
    c3
    cn
    @134
    3nn
    nnuz
    eleqtri
    c1
    c3
    hashfzo
    ax-mp
    3m1e2
    eqtri
    a1i
    oveq2d
    3eqtrd
    oveq1d
    @105
    @34
    @37
    @122
    @105
    @36
    @132
    sqcld
    mulcomd
    eqtr4d
    3eqtr3d
    oveq1d
    itgeq2dv
    3eqtr3d
end
