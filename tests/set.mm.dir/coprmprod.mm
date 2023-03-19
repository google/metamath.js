include "cfn.mm"
include "wcel.mm"
include "cn.mm"
include "wss.mm"
include "w3a.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wral.mm"
include "csn.mm"
include "cdif.mm"
include "cprod.mm"
include "wi.mm"
include "c0.mm"
include "cun.mm"
include "sseq1.mm"
include "3anbi1d.mm"
include "raleq.mm"
include "difeq1.mm"
include "raleqdv.mm"
include "raleqbi1dv.mm"
include "3anbi123d.mm"
include "prodeq1.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "prod0.mm"
include "a1i.mm"
include "cz.mm"
include "nnz.mm"
include "1gcd.mm"
include "syl.mm"
include "eqtrd.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "wn.mm"
include "wa.mm"
include "cmul.mm"
include "nfv.mm"
include "nfcv.mm"
include "simprl.mm"
include "unss.mm"
include "vex.mm"
include "snss.mm"
include "biimpri.mm"
include "adantl.mm"
include "sylbir.mm"
include "adantr.mm"
include "simprr.mm"
include "simpll3.mm"
include "simpl.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "nncnd.mm"
include "fveq2.mm"
include "simpr.mm"
include "3adant2.mm"
include "fprodsplitsn.mm"
include "fprodnncl.mm"
include "nnzd.mm"
include "zmulcld.mm"
include "gcdcom.mm"
include "syl2anc.mm"
include "ex.mm"
include "com12.mm"
include "imp.mm"
include "simpl2.mm"
include "3jca.mm"
include "idd.mm"
include "3anim123d.mm"
include "ssun1.mm"
include "ssralv.mm"
include "mp1i.mm"
include "ssdifd.mm"
include "ralimdva.mm"
include "syld.mm"
include "imim1d.mm"
include "imp31.mm"
include "rpmulgcd.mm"
include "wo.mm"
include "vsnid.mm"
include "olci.mm"
include "elun.mm"
include "mpbir.mm"
include "rspcv.mm"
include "wb.mm"
include "mpbird.mm"
include "3adant3.mm"
include "3eqtrd.mm"
include "exp31.mm"
include "findcard2s.mm"
include "3expd.mm"
include "3imp.mm"

theorem coprmprod
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint F m
  disjoint M m
  disjoint M n
  disjoint m n
  disjoint N m
  disjoint N n
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint N x
  disjoint N y
  disjoint N z
  assert |- ( ( ( M e. Fin /\ M C_ NN /\ N e. NN ) /\ F : NN --> NN /\ A. m e. M ( ( F ` m ) gcd N ) = 1 ) -> ( A. m e. M A. n e. ( M \ { m } ) ( ( F ` m ) gcd ( F ` n ) ) = 1 -> ( prod_ m e. M ( F ` m ) gcd N ) = 1 ) )

  proof
    cM
    cfn
    wcel
    #
    cM
    cn
    wss
    #
    cN
    cn
    wcel
    #
    w3a
    cn
    cn
    cF
    wf
    #
    vm
    cv
    #
    cF
    cfv
    #
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    vm
    cM
    wral
    #
    @5
    vn
    cv
    cF
    cfv
    cgcd
    co
    c1
    wceq
    #
    vn
    cM
    @4
    csn
    #
    cdif
    #
    wral
    #
    vm
    cM
    wral
    #
    cM
    @5
    vm
    cprod
    #
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    wi
    #
    @0
    @1
    @2
    @3
    @8
    @17
    wi
    #
    wi
    @0
    @1
    @2
    @3
    @18
    @0
    @1
    @2
    @3
    w3a
    #
    @8
    @13
    @16
    vx
    cv
    #
    cn
    wss
    #
    @2
    @3
    w3a
    #
    @7
    vm
    @20
    wral
    #
    @9
    vn
    @20
    @10
    cdif
    #
    wral
    #
    vm
    @20
    wral
    #
    w3a
    #
    @20
    @5
    vm
    cprod
    #
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    wi
    c0
    cn
    wss
    #
    @2
    @3
    w3a
    #
    @7
    vm
    c0
    wral
    #
    @9
    vn
    c0
    @10
    cdif
    #
    wral
    #
    vm
    c0
    wral
    #
    w3a
    #
    c0
    @5
    vm
    cprod
    #
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    wi
    vy
    cv
    #
    cn
    wss
    #
    @2
    @3
    w3a
    #
    @7
    vm
    @41
    wral
    #
    @9
    vn
    @41
    @10
    cdif
    #
    wral
    #
    vm
    @41
    wral
    #
    w3a
    #
    @41
    @5
    vm
    cprod
    #
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    wi
    #
    @41
    vz
    cv
    #
    csn
    #
    cun
    #
    cn
    wss
    #
    @2
    @3
    w3a
    #
    @7
    vm
    @55
    wral
    #
    @9
    vn
    @55
    @10
    cdif
    #
    wral
    #
    vm
    @55
    wral
    #
    w3a
    #
    @55
    @5
    vm
    cprod
    #
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    wi
    @19
    @8
    @13
    w3a
    #
    @16
    wi
    vx
    vy
    vz
    cM
    @20
    c0
    wceq
    #
    @27
    @37
    @30
    @40
    @67
    @22
    @32
    @23
    @33
    @26
    @36
    @67
    @21
    @31
    @2
    @3
    @20
    c0
    cn
    sseq1
    3anbi1d
    @7
    vm
    @20
    c0
    raleq
    @25
    @35
    vm
    @20
    c0
    @67
    @9
    vn
    @24
    @34
    @20
    c0
    @10
    difeq1
    raleqdv
    raleqbi1dv
    3anbi123d
    @67
    @29
    @39
    c1
    @67
    @28
    @38
    cN
    cgcd
    @20
    c0
    @5
    vm
    prodeq1
    oveq1d
    eqeq1d
    imbi12d
    @20
    @41
    wceq
    #
    @27
    @48
    @30
    @51
    @68
    @22
    @43
    @23
    @44
    @26
    @47
    @68
    @21
    @42
    @2
    @3
    @20
    @41
    cn
    sseq1
    3anbi1d
    @7
    vm
    @20
    @41
    raleq
    @25
    @46
    vm
    @20
    @41
    @68
    @9
    vn
    @24
    @45
    @20
    @41
    @10
    difeq1
    raleqdv
    raleqbi1dv
    3anbi123d
    @68
    @29
    @50
    c1
    @68
    @28
    @49
    cN
    cgcd
    @20
    @41
    @5
    vm
    prodeq1
    oveq1d
    eqeq1d
    imbi12d
    @20
    @55
    wceq
    #
    @27
    @62
    @30
    @65
    @69
    @22
    @57
    @23
    @58
    @26
    @61
    @69
    @21
    @56
    @2
    @3
    @20
    @55
    cn
    sseq1
    3anbi1d
    @7
    vm
    @20
    @55
    raleq
    @25
    @60
    vm
    @20
    @55
    @69
    @9
    vn
    @24
    @59
    @20
    @55
    @10
    difeq1
    raleqdv
    raleqbi1dv
    3anbi123d
    @69
    @29
    @64
    c1
    @69
    @28
    @63
    cN
    cgcd
    @20
    @55
    @5
    vm
    prodeq1
    oveq1d
    eqeq1d
    imbi12d
    @20
    cM
    wceq
    #
    @27
    @66
    @30
    @16
    @70
    @22
    @19
    @23
    @8
    @26
    @13
    @70
    @21
    @1
    @2
    @3
    @20
    cM
    cn
    sseq1
    3anbi1d
    @7
    vm
    @20
    cM
    raleq
    @25
    @12
    vm
    @20
    cM
    @70
    @9
    vn
    @24
    @11
    @20
    cM
    @10
    difeq1
    raleqdv
    raleqbi1dv
    3anbi123d
    @70
    @29
    @15
    c1
    @70
    @28
    @14
    cN
    cgcd
    @20
    cM
    @5
    vm
    prodeq1
    oveq1d
    eqeq1d
    imbi12d
    @32
    @33
    @40
    @36
    @2
    @31
    @40
    @3
    @2
    @39
    c1
    cN
    cgcd
    co
    #
    c1
    @2
    @38
    c1
    cN
    cgcd
    @38
    c1
    wceq
    @2
    @5
    vm
    prod0
    a1i
    oveq1d
    @2
    cN
    cz
    wcel
    #
    @71
    c1
    wceq
    cN
    nnz
    #
    cN
    1gcd
    syl
    eqtrd
    3ad2ant2
    3ad2ant1
    @41
    cfn
    wcel
    #
    @53
    @41
    wcel
    #
    wn
    #
    wa
    #
    @52
    @62
    @65
    @77
    @52
    wa
    #
    @62
    wa
    #
    @64
    cN
    @49
    @53
    cF
    cfv
    #
    cmul
    co
    #
    cgcd
    co
    #
    cN
    @80
    cgcd
    co
    #
    c1
    @78
    @62
    @64
    @82
    wceq
    #
    @77
    @62
    @84
    wi
    @52
    @62
    @77
    @84
    @57
    @58
    @77
    @84
    wi
    @61
    @57
    @77
    @84
    @57
    @77
    wa
    #
    @64
    @81
    cN
    cgcd
    co
    #
    @82
    @85
    @63
    @81
    cN
    cgcd
    @85
    @41
    @53
    @5
    @80
    vm
    cn
    @85
    vm
    nfv
    vm
    @80
    nfcv
    @57
    @74
    @76
    simprl
    #
    @57
    @53
    cn
    wcel
    #
    @77
    @56
    @2
    @88
    @3
    @56
    @42
    @54
    cn
    wss
    #
    wa
    #
    @88
    @41
    @54
    cn
    unss
    #
    @89
    @88
    @42
    @88
    @89
    @53
    cn
    vz
    vex
    snss
    biimpri
    adantl
    sylbir
    #
    3ad2ant1
    adantr
    @57
    @74
    @76
    simprr
    @85
    @4
    @41
    wcel
    #
    wa
    #
    @5
    @94
    cn
    cn
    @4
    cF
    @56
    @2
    @3
    @77
    @93
    simpll3
    @85
    @41
    cn
    @4
    @57
    @42
    @77
    @56
    @2
    @42
    @3
    @56
    @90
    @42
    @91
    @42
    @89
    simpl
    sylbir
    #
    3ad2ant1
    adantr
    sselda
    ffvelrnd
    #
    nncnd
    @4
    @53
    cF
    fveq2
    #
    @85
    @80
    @57
    @80
    cn
    wcel
    #
    @77
    @56
    @3
    @98
    @2
    @56
    @3
    wa
    cn
    cn
    @53
    cF
    @56
    @3
    simpr
    @56
    @88
    @3
    @92
    adantr
    ffvelrnd
    3adant2
    #
    adantr
    #
    nncnd
    fprodsplitsn
    oveq1d
    @85
    @81
    cz
    wcel
    @72
    @86
    @82
    wceq
    @85
    @49
    @80
    @85
    @49
    @85
    @41
    @5
    vm
    @87
    @96
    fprodnncl
    #
    nnzd
    #
    @85
    @80
    @100
    nnzd
    zmulcld
    @57
    @72
    @77
    @2
    @56
    @72
    @3
    @73
    3ad2ant2
    #
    adantr
    #
    @81
    cN
    gcdcom
    syl2anc
    eqtrd
    ex
    3ad2ant1
    com12
    adantr
    imp
    @79
    @2
    @49
    cn
    wcel
    #
    @98
    w3a
    #
    cN
    @49
    cgcd
    co
    #
    c1
    wceq
    @82
    @83
    wceq
    @78
    @62
    @106
    @77
    @62
    @106
    wi
    @52
    @62
    @77
    @106
    @57
    @58
    @77
    @106
    wi
    @61
    @57
    @77
    @106
    @85
    @2
    @105
    @98
    @56
    @2
    @3
    @77
    simpl2
    @101
    @100
    3jca
    ex
    3ad2ant1
    com12
    adantr
    imp
    @79
    @107
    @50
    c1
    @78
    @62
    @107
    @50
    wceq
    #
    @77
    @62
    @108
    wi
    @52
    @62
    @77
    @108
    @57
    @58
    @77
    @108
    wi
    @61
    @57
    @77
    @108
    @85
    @72
    @49
    cz
    wcel
    @108
    @104
    @102
    cN
    @49
    gcdcom
    syl2anc
    ex
    3ad2ant1
    com12
    adantr
    imp
    @77
    @52
    @62
    @51
    @77
    @62
    @48
    @51
    @77
    @57
    @43
    @58
    @44
    @61
    @47
    @77
    @56
    @42
    @2
    @2
    @3
    @3
    @56
    @42
    wi
    @77
    @95
    a1i
    @77
    @2
    idd
    @77
    @3
    idd
    3anim123d
    @41
    @55
    wss
    #
    @58
    @44
    wi
    @77
    @41
    @54
    ssun1
    #
    @7
    vm
    @41
    @55
    ssralv
    mp1i
    @77
    @61
    @60
    vm
    @41
    wral
    #
    @47
    @109
    @61
    @111
    wi
    @77
    @110
    @60
    vm
    @41
    @55
    ssralv
    mp1i
    @77
    @60
    @46
    vm
    @41
    @77
    @93
    wa
    #
    @45
    @59
    wss
    @60
    @46
    wi
    @112
    @41
    @55
    @10
    @109
    @112
    @110
    a1i
    ssdifd
    @9
    vn
    @45
    @59
    ssralv
    syl
    ralimdva
    syld
    3anim123d
    imim1d
    imp31
    eqtrd
    cN
    @49
    @80
    rpmulgcd
    syl2anc
    @62
    @83
    c1
    wceq
    #
    @78
    @57
    @58
    @113
    @61
    @57
    @58
    wa
    @113
    @80
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    @57
    @58
    @115
    @53
    @55
    wcel
    #
    @58
    @115
    wi
    @57
    @116
    @75
    @53
    @54
    wcel
    #
    wo
    @117
    @75
    vz
    vsnid
    olci
    @53
    @41
    @54
    elun
    mpbir
    @7
    @115
    vm
    @53
    @55
    @4
    @53
    wceq
    #
    @6
    @114
    c1
    @118
    @5
    @80
    cN
    cgcd
    @97
    oveq1d
    eqeq1d
    rspcv
    mp1i
    imp
    @57
    @113
    @115
    wb
    @58
    @57
    @83
    @114
    c1
    @57
    @72
    @80
    cz
    wcel
    @83
    @114
    wceq
    @103
    @57
    @80
    @99
    nnzd
    cN
    @80
    gcdcom
    syl2anc
    eqeq1d
    adantr
    mpbird
    3adant3
    adantl
    3eqtrd
    exp31
    findcard2s
    3expd
    3expd
    3imp
    3imp
end
