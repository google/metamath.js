include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cmin.mm"
include "0red.mm"
include "c2.mm"
include "cmul.mm"
include "cdiv.mm"
include "cexp.mm"
include "cr.mm"
include "cv.mm"
include "cc.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "wa.mm"
include "simpr.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "1nn.mm"
include "2cnd.mm"
include "1cnd.mm"
include "mulcld.mm"
include "addcld.mm"
include "wne.mm"
include "c3.mm"
include "2t1e2.mm"
include "oveq1i.mm"
include "2p1e3.mm"
include "eqtri.mm"
include "3ne0.mm"
include "eqnetri.mm"
include "reccld.mm"
include "nncn.mm"
include "1red.mm"
include "2re.mm"
include "nnre.mm"
include "remulcld.mm"
include "readdcld.mm"
include "0lt1.mm"
include "crp.mm"
include "2rp.mm"
include "nnrp.mm"
include "rpmulcld.mm"
include "ltaddrp2d.mm"
include "lttrd.mm"
include "gt0ne0d.mm"
include "cn0.mm"
include "2nn0.mm"
include "1nn0.mm"
include "nn0mulcld.mm"
include "expcld.mm"
include "fvmptd.mm"
include "1re.mm"
include "remulcli.mm"
include "readdcli.mm"
include "rereccli.mm"
include "rereccld.mm"
include "reexpcld.mm"
include "eqeltrd.mm"
include "clog.mm"
include "stirlinglem2.mm"
include "relogcld.mm"
include "nfcv.mm"
include "cfa.mm"
include "csqrt.mm"
include "ceu.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fvmptf.mm"
include "mpdan.mm"
include "peano2nn.mm"
include "syl.mm"
include "syl2anc.mm"
include "resubcld.mm"
include "cle.mm"
include "0le2.mm"
include "0le1.mm"
include "mulge0d.mm"
include "ge0p1rpd.mm"
include "rpreccld.mm"
include "rpge0d.mm"
include "cz.mm"
include "2z.mm"
include "1z.mm"
include "zmulcld.mm"
include "rpexpcld.mm"
include "rpgt0d.mm"
include "cseq.mm"
include "cuz.mm"
include "eqid.mm"
include "peano2zd.mm"
include "nnuz.mm"
include "oveq2.mm"
include "adantl.mm"
include "adantr.mm"
include "nnnn0.mm"
include "stirlinglem9.mm"
include "clim2ser.mm"
include "wss.mm"
include "uznnssnn.mm"
include "mp2b.mm"
include "sseld.mm"
include "imdistani.mm"
include "eluzelre.mm"
include "sseli.mm"
include "1p1e2.mm"
include "eluzle.mm"
include "syl5eqbrr.mm"
include "letrd.mm"
include "divge0d.mm"
include "expge0d.mm"
include "breqtrrd.mm"
include "iserge0.mm"
include "seq1.mm"
include "mp1i.mm"
include "breqtrd.mm"
include "leadd1dd.mm"
include "addid2d.mm"
include "recnd.mm"
include "subcld.mm"
include "npcand.mm"
include "3brtr3d.mm"
include "ltletrd.mm"
include "posdifd.mm"
include "mpbird.mm"

theorem stirlinglem11
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cK: class K
  let cN: class N
  let vj: setvar j
  let vx: setvar x
  assume stirlinglem11.1: |- A = ( n e. NN |-> ( ( ! ` n ) / ( ( sqrt ` ( 2 x. n ) ) x. ( ( n / _e ) ^ n ) ) ) )
  assume stirlinglem11.2: |- B = ( n e. NN |-> ( log ` ( A ` n ) ) )
  assume stirlinglem11.3: |- K = ( k e. NN |-> ( ( 1 / ( ( 2 x. k ) + 1 ) ) x. ( ( 1 / ( ( 2 x. N ) + 1 ) ) ^ ( 2 x. k ) ) ) )

  disjoint k n
  disjoint K n
  disjoint N k
  disjoint N n
  disjoint j k
  disjoint B j
  disjoint K j
  disjoint N j
  disjoint k x
  assert |- ( N e. NN -> ( B ` ( N + 1 ) ) < ( B ` N ) )

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
    cB
    cfv
    #
    cN
    cB
    cfv
    #
    clt
    wbr
    cc0
    @3
    @2
    cmin
    co
    #
    clt
    wbr
    @0
    cc0
    c1
    cK
    cfv
    #
    @4
    @0
    0red
    #
    @0
    @5
    c1
    c2
    c1
    cmul
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    c1
    c2
    cN
    cmul
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    @7
    cexp
    co
    #
    cmul
    co
    #
    cr
    @0
    vk
    c1
    c1
    c2
    vk
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    @12
    @16
    cexp
    co
    #
    cmul
    co
    #
    @14
    cn
    cK
    cc
    cK
    vk
    cn
    @20
    cmpt
    wceq
    #
    @0
    stirlinglem11.3
    a1i
    @0
    @15
    c1
    wceq
    #
    wa
    #
    @18
    @9
    @19
    @13
    cmul
    @23
    @17
    @8
    c1
    cdiv
    @23
    @16
    @7
    c1
    caddc
    @23
    @15
    c1
    c2
    cmul
    @0
    @22
    simpr
    oveq2d
    #
    oveq1d
    oveq2d
    @23
    @16
    @7
    @12
    cexp
    @24
    oveq2d
    oveq12d
    c1
    cn
    wcel
    #
    @0
    1nn
    a1i
    #
    @0
    @9
    @13
    @0
    @8
    @0
    @7
    c1
    @0
    c2
    c1
    @0
    2cnd
    #
    @0
    1cnd
    #
    mulcld
    @28
    addcld
    @8
    cc0
    wne
    @0
    @8
    c3
    cc0
    @8
    c2
    c1
    caddc
    co
    c3
    @7
    c2
    c1
    caddc
    2t1e2
    oveq1i
    2p1e3
    eqtri
    3ne0
    eqnetri
    #
    a1i
    reccld
    @0
    @12
    @7
    @0
    @11
    @0
    @10
    c1
    @0
    c2
    cN
    @27
    cN
    nncn
    #
    mulcld
    @28
    addcld
    @0
    @11
    @0
    cc0
    c1
    @11
    @6
    @0
    1red
    #
    @0
    @10
    c1
    @0
    c2
    cN
    c2
    cr
    wcel
    #
    @0
    2re
    a1i
    #
    cN
    nnre
    #
    remulcld
    #
    @31
    readdcld
    #
    cc0
    c1
    clt
    wbr
    #
    @0
    0lt1
    a1i
    @0
    c1
    @10
    @31
    @0
    c2
    cN
    c2
    crp
    wcel
    #
    @0
    2rp
    a1i
    cN
    nnrp
    #
    rpmulcld
    ltaddrp2d
    lttrd
    gt0ne0d
    #
    reccld
    @0
    c2
    c1
    c2
    cn0
    wcel
    #
    @0
    2nn0
    a1i
    c1
    cn0
    wcel
    @0
    1nn0
    a1i
    nn0mulcld
    #
    expcld
    mulcld
    #
    fvmptd
    #
    @0
    @9
    @13
    @9
    cr
    wcel
    @0
    @8
    @7
    c1
    c2
    c1
    2re
    1re
    remulcli
    1re
    readdcli
    @29
    rereccli
    a1i
    @0
    @12
    @7
    @0
    @11
    @36
    @40
    rereccld
    @42
    reexpcld
    remulcld
    eqeltrd
    #
    @0
    @3
    @2
    @0
    @3
    cN
    cA
    cfv
    #
    clog
    cfv
    #
    cr
    @0
    @47
    cr
    wcel
    @3
    @47
    wceq
    @0
    @46
    cA
    vn
    cN
    stirlinglem11.1
    stirlinglem2
    relogcld
    #
    vn
    cN
    vn
    cv
    #
    cA
    cfv
    #
    clog
    cfv
    #
    @47
    cn
    cB
    cr
    vn
    cN
    nfcv
    #
    vn
    @46
    clog
    vn
    clog
    nfcv
    #
    vn
    cN
    cA
    vn
    cA
    vn
    cn
    @49
    cfa
    cfv
    c2
    @49
    cmul
    co
    #
    csqrt
    cfv
    @49
    ceu
    cdiv
    co
    @49
    cexp
    co
    cmul
    co
    cdiv
    co
    #
    cmpt
    stirlinglem11.1
    vn
    cn
    @55
    nfmpt1
    nfcxfr
    #
    @52
    nffv
    nffv
    @49
    cN
    wceq
    @50
    @46
    clog
    @49
    cN
    cA
    fveq2
    fveq2d
    stirlinglem11.2
    fvmptf
    mpdan
    @48
    eqeltrd
    #
    @0
    @2
    @1
    cA
    cfv
    #
    clog
    cfv
    #
    cr
    @0
    @1
    cn
    wcel
    #
    @59
    cr
    wcel
    @2
    @59
    wceq
    cN
    peano2nn
    #
    @0
    @58
    @0
    @60
    @58
    crp
    wcel
    @61
    cA
    vn
    @1
    stirlinglem11.1
    stirlinglem2
    syl
    relogcld
    #
    vn
    @1
    @51
    @59
    cn
    cB
    cr
    vn
    @1
    nfcv
    #
    vn
    @58
    clog
    @53
    vn
    @1
    cA
    @56
    @63
    nffv
    nffv
    @49
    @1
    wceq
    @50
    @58
    clog
    @49
    @1
    cA
    fveq2
    fveq2d
    stirlinglem11.2
    fvmptf
    syl2anc
    @62
    eqeltrd
    #
    resubcld
    #
    @0
    @5
    @0
    @5
    @14
    crp
    @44
    @0
    @9
    @13
    @0
    @8
    @0
    @7
    @0
    c2
    c1
    @33
    @31
    remulcld
    @0
    c2
    c1
    @33
    @31
    cc0
    c2
    cle
    wbr
    #
    @0
    0le2
    a1i
    #
    cc0
    c1
    cle
    wbr
    #
    @0
    0le1
    a1i
    mulge0d
    ge0p1rpd
    rpreccld
    @0
    @12
    @7
    @0
    @11
    @0
    @10
    @35
    @0
    c2
    cN
    @33
    @34
    @67
    @0
    cN
    @39
    rpge0d
    #
    mulge0d
    ge0p1rpd
    rpreccld
    @0
    c2
    c1
    c2
    cz
    wcel
    @0
    2z
    a1i
    c1
    cz
    wcel
    #
    @0
    1z
    a1i
    #
    zmulcld
    rpexpcld
    rpmulcld
    eqeltrd
    rpgt0d
    @0
    cc0
    @5
    caddc
    co
    @4
    @5
    cmin
    co
    #
    @5
    caddc
    co
    @5
    @4
    cle
    @0
    cc0
    @72
    @5
    @6
    @0
    @4
    @5
    @65
    @45
    resubcld
    @45
    @0
    cc0
    @4
    c1
    caddc
    cK
    c1
    cseq
    cfv
    #
    cmin
    co
    #
    @72
    cle
    @0
    @74
    vj
    cK
    c1
    c1
    caddc
    co
    #
    @75
    cuz
    cfv
    #
    @76
    eqid
    @0
    c1
    @71
    peano2zd
    @0
    @4
    vj
    cK
    c1
    c1
    cn
    nnuz
    @26
    @0
    vj
    cv
    #
    cn
    wcel
    #
    wa
    #
    @77
    cK
    cfv
    #
    c1
    c2
    @77
    cmul
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    @12
    @81
    cexp
    co
    #
    cmul
    co
    #
    cc
    @79
    vk
    @77
    @20
    @85
    cn
    cK
    cc
    @21
    @79
    stirlinglem11.3
    a1i
    @15
    @77
    wceq
    #
    @20
    @85
    wceq
    @79
    @86
    @18
    @83
    @19
    @84
    cmul
    @86
    @17
    @82
    c1
    cdiv
    @86
    @16
    @81
    c1
    caddc
    @15
    @77
    c2
    cmul
    oveq2
    #
    oveq1d
    oveq2d
    @86
    @16
    @81
    @12
    cexp
    @87
    oveq2d
    oveq12d
    adantl
    @0
    @78
    simpr
    @79
    @83
    @84
    @79
    @82
    @79
    @81
    c1
    @79
    c2
    @77
    @79
    2cnd
    #
    @78
    @77
    cc
    wcel
    @0
    @77
    nncn
    adantl
    mulcld
    @79
    1cnd
    #
    addcld
    #
    @79
    @82
    @79
    cc0
    c1
    @82
    @79
    0red
    @79
    1red
    #
    @79
    @81
    c1
    @79
    c2
    @77
    @32
    @79
    2re
    a1i
    @78
    @77
    cr
    wcel
    #
    @0
    @77
    nnre
    #
    adantl
    #
    remulcld
    @91
    readdcld
    @37
    @79
    0lt1
    a1i
    @79
    c1
    @81
    @91
    @79
    c2
    @77
    @38
    @79
    2rp
    a1i
    @78
    @77
    crp
    wcel
    @0
    @77
    nnrp
    #
    adantl
    rpmulcld
    ltaddrp2d
    lttrd
    gt0ne0d
    reccld
    @79
    @12
    @81
    @79
    @11
    @79
    @10
    c1
    @79
    c2
    cN
    @88
    @0
    cN
    cc
    wcel
    @78
    @30
    adantr
    mulcld
    @89
    addcld
    @0
    @11
    cc0
    wne
    #
    @78
    @40
    adantr
    reccld
    @79
    c2
    @77
    @41
    @79
    2nn0
    a1i
    @78
    @77
    cn0
    wcel
    @0
    @77
    nnnn0
    adantl
    nn0mulcld
    #
    expcld
    #
    mulcld
    fvmptd
    #
    @79
    @83
    @84
    @79
    @82
    @90
    @78
    @82
    cc0
    wne
    #
    @0
    @78
    @82
    @78
    cc0
    c1
    @82
    @78
    0red
    @78
    1red
    #
    @78
    @81
    c1
    @78
    c2
    @77
    @32
    @78
    2re
    a1i
    @93
    remulcld
    @101
    readdcld
    @37
    @78
    0lt1
    a1i
    @78
    c1
    @81
    @101
    @78
    c2
    @77
    @38
    @78
    2rp
    a1i
    @95
    rpmulcld
    ltaddrp2d
    lttrd
    gt0ne0d
    #
    adantl
    reccld
    @98
    mulcld
    eqeltrd
    cA
    cB
    vk
    vn
    vn
    cn
    c1
    @54
    caddc
    co
    c2
    cdiv
    co
    @49
    c1
    caddc
    co
    @49
    cdiv
    co
    clog
    cfv
    cmul
    co
    c1
    cmin
    co
    cmpt
    #
    cK
    cN
    stirlinglem11.1
    stirlinglem11.2
    @103
    eqid
    stirlinglem11.3
    stirlinglem9
    clim2ser
    @0
    @77
    @76
    wcel
    #
    wa
    #
    @80
    @85
    cr
    @105
    @79
    @80
    @85
    wceq
    @0
    @104
    @78
    @0
    @76
    cn
    @77
    @76
    cn
    wss
    #
    @0
    @25
    @75
    cn
    wcel
    @106
    1nn
    c1
    peano2nn
    @75
    uznnssnn
    mp2b
    #
    a1i
    sseld
    imdistani
    #
    @99
    syl
    #
    @105
    @83
    @84
    @104
    @83
    cr
    wcel
    @0
    @104
    @82
    @104
    @81
    c1
    @104
    c2
    @77
    @32
    @104
    2re
    a1i
    #
    @75
    @77
    eluzelre
    #
    remulcld
    @104
    1red
    readdcld
    @104
    @78
    @100
    @76
    cn
    @77
    @107
    sseli
    @102
    syl
    rereccld
    adantl
    #
    @105
    @12
    @81
    @105
    @11
    @0
    @11
    cr
    wcel
    @104
    @36
    adantr
    @0
    @96
    @104
    @40
    adantr
    rereccld
    #
    @105
    @79
    @81
    cn0
    wcel
    @108
    @97
    syl
    #
    reexpcld
    #
    remulcld
    eqeltrd
    @105
    cc0
    @85
    @80
    cle
    @105
    @83
    @84
    @112
    @115
    @105
    c1
    @82
    @105
    1red
    #
    @105
    @81
    @105
    c2
    @77
    @32
    @105
    2re
    a1i
    #
    @105
    @79
    @92
    @108
    @94
    syl
    #
    remulcld
    @105
    c2
    @77
    @117
    @118
    @66
    @105
    0le2
    a1i
    #
    @104
    cc0
    @77
    cle
    wbr
    @0
    @104
    cc0
    c2
    @77
    @104
    0red
    @110
    @111
    @66
    @104
    0le2
    a1i
    @104
    c2
    @75
    @77
    cle
    1p1e2
    @75
    @77
    eluzle
    syl5eqbrr
    letrd
    adantl
    mulge0d
    ge0p1rpd
    @68
    @105
    0le1
    a1i
    #
    divge0d
    @105
    @12
    @81
    @113
    @114
    @105
    c1
    @11
    @116
    @105
    @10
    @105
    c2
    cN
    @117
    @0
    cN
    cr
    wcel
    @104
    @34
    adantr
    #
    remulcld
    @105
    c2
    cN
    @117
    @121
    @119
    @0
    cc0
    cN
    cle
    wbr
    @104
    @69
    adantr
    mulge0d
    ge0p1rpd
    @120
    divge0d
    expge0d
    mulge0d
    @109
    breqtrrd
    iserge0
    @0
    @73
    @5
    @4
    cmin
    @70
    @73
    @5
    wceq
    @0
    1z
    caddc
    cK
    c1
    seq1
    mp1i
    oveq2d
    breqtrd
    leadd1dd
    @0
    @5
    @0
    @5
    @14
    cc
    @44
    @43
    eqeltrd
    #
    addid2d
    @0
    @4
    @5
    @0
    @3
    @2
    @0
    @3
    @57
    recnd
    @0
    @2
    @64
    recnd
    subcld
    @122
    npcand
    3brtr3d
    ltletrd
    @0
    @2
    @3
    @64
    @57
    posdifd
    mpbird
end
