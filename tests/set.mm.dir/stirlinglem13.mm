include "crn.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "wcel.mm"
include "cli.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wral.mm"
include "cfv.mm"
include "clog.mm"
include "wceq.mm"
include "cn.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "wa.mm"
include "simpr.mm"
include "stirlinglem2.mm"
include "relogcld.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "rexlimiva.mm"
include "sylbi.mm"
include "ssriv.mm"
include "c1.mm"
include "1nn.mm"
include "crp.mm"
include "relogcl.mm"
include "mp2b.mm"
include "nfcv.mm"
include "cfa.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "ceu.mm"
include "cdiv.mm"
include "cexp.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fvmptf.mm"
include "mp2an.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "eqeltri.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "mpbir.mm"
include "ne0ii.mm"
include "c4.mm"
include "cmin.mm"
include "4re.mm"
include "4ne0.mm"
include "rereccli.mm"
include "resubcli.mm"
include "caddc.mm"
include "eqid.mm"
include "stirlinglem12.mm"
include "rgen.mm"
include "breq1.mm"
include "ralbidv.mm"
include "wfn.mm"
include "fnmpt.mm"
include "fvelrnb.mm"
include "sylib.mm"
include "nfra1.mm"
include "nfv.mm"
include "nfan.mm"
include "w3a.mm"
include "simp1l.mm"
include "simp2.mm"
include "rsp.mm"
include "sylc.mm"
include "simp3.mm"
include "breqtrd.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "reximi.mm"
include "infrecl.mm"
include "mp3an.mm"
include "wtru.mm"
include "nnuz.mm"
include "1zzd.mm"
include "wf.mm"
include "fmpti.mm"
include "a1i.mm"
include "peano2nn.mm"
include "cc.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "faccl.mm"
include "nncn.mm"
include "3syl.mm"
include "2cnd.mm"
include "1cnd.mm"
include "addcld.mm"
include "mulcld.mm"
include "sqrtcld.mm"
include "ere.mm"
include "recni.mm"
include "cc0.mm"
include "0re.mm"
include "epos.mm"
include "gtneii.mm"
include "divcld.mm"
include "expcld.mm"
include "2rp.mm"
include "nnre.mm"
include "1red.mm"
include "0le1.mm"
include "nnge1.mm"
include "letrd.mm"
include "ge0p1rpd.mm"
include "rpmulcld.mm"
include "sqrtgt0d.mm"
include "gt0ne0d.mm"
include "nnne0d.mm"
include "divne0d.mm"
include "nnz.mm"
include "peano2zd.mm"
include "expne0d.mm"
include "mulne0d.mm"
include "fvmptd.mm"
include "nnrp.mm"
include "rpsqrtcld.mm"
include "epr.mm"
include "rpdivcld.mm"
include "rpexpcld.mm"
include "syl2anc.mm"
include "ffvelrni.mm"
include "stirlinglem11.mm"
include "ltled.mm"
include "adantl.mm"
include "climinf.mm"
include "trud.mm"
include "breq2.mm"

theorem stirlinglem13
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vd: setvar d
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume stirlinglem13.1: |- A = ( n e. NN |-> ( ( ! ` n ) / ( ( sqrt ` ( 2 x. n ) ) x. ( ( n / _e ) ^ n ) ) ) )
  assume stirlinglem13.2: |- B = ( n e. NN |-> ( log ` ( A ` n ) ) )

  disjoint B d
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint j z
  disjoint n z
  disjoint A j
  disjoint B j
  disjoint B x
  disjoint B y
  disjoint k x
  assert |- E. d e. RR B ~~> d

  proof
    cB
    crn
    #
    cr
    clt
    cinf
    #
    cr
    wcel
    #
    cB
    @1
    cli
    wbr
    #
    cB
    vd
    cv
    #
    cli
    wbr
    #
    vd
    cr
    wrex
    @0
    cr
    wss
    @0
    c0
    wne
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vy
    @0
    wral
    #
    vx
    cr
    wrex
    #
    @2
    vy
    @0
    cr
    @7
    @0
    wcel
    #
    @7
    vn
    cv
    #
    cA
    cfv
    #
    clog
    cfv
    #
    wceq
    #
    vn
    cn
    wrex
    #
    @7
    cr
    wcel
    #
    @7
    cvv
    wcel
    @11
    @16
    wb
    vy
    vex
    vn
    cn
    @14
    @7
    cB
    cvv
    stirlinglem13.2
    elrnmpt
    ax-mp
    @15
    @17
    vn
    cn
    @12
    cn
    wcel
    #
    @15
    wa
    @7
    @14
    cr
    @18
    @15
    simpr
    @18
    @14
    cr
    wcel
    #
    @15
    @18
    @13
    cA
    vn
    @12
    stirlinglem13.1
    stirlinglem2
    relogcld
    #
    adantr
    eqeltrd
    rexlimiva
    sylbi
    ssriv
    c1
    cB
    cfv
    #
    @0
    @21
    @0
    wcel
    #
    @21
    vj
    cv
    #
    cA
    cfv
    #
    clog
    cfv
    #
    wceq
    #
    vj
    cn
    wrex
    #
    c1
    cn
    wcel
    #
    @21
    c1
    cA
    cfv
    #
    clog
    cfv
    #
    wceq
    #
    @27
    1nn
    @28
    @30
    cr
    wcel
    #
    @31
    1nn
    @28
    @29
    crp
    wcel
    @32
    1nn
    cA
    vn
    c1
    stirlinglem13.1
    stirlinglem2
    @29
    relogcl
    mp2b
    #
    vn
    c1
    @14
    @30
    cn
    cB
    cr
    vn
    c1
    nfcv
    #
    vn
    @29
    clog
    vn
    clog
    nfcv
    #
    vn
    c1
    cA
    vn
    cA
    vn
    cn
    @12
    cfa
    cfv
    #
    c2
    @12
    cmul
    co
    #
    csqrt
    cfv
    #
    @12
    ceu
    cdiv
    co
    #
    @12
    cexp
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    cmpt
    #
    stirlinglem13.1
    vn
    cn
    @42
    nfmpt1
    nfcxfr
    #
    @34
    nffv
    nffv
    @12
    c1
    wceq
    @13
    @29
    clog
    @12
    c1
    cA
    fveq2
    fveq2d
    stirlinglem13.2
    fvmptf
    mp2an
    #
    @26
    @31
    vj
    c1
    cn
    @23
    c1
    wceq
    #
    @25
    @30
    @21
    @46
    @24
    @29
    clog
    @23
    c1
    cA
    fveq2
    fveq2d
    eqeq2d
    rspcev
    mp2an
    @21
    cr
    wcel
    @22
    @27
    wb
    @21
    @30
    cr
    @45
    @33
    eqeltri
    #
    vj
    cn
    @25
    @21
    cB
    cr
    cB
    vn
    cn
    @14
    cmpt
    vj
    cn
    @25
    cmpt
    stirlinglem13.2
    vn
    vj
    cn
    @14
    @25
    vj
    @14
    nfcv
    vn
    @24
    clog
    @35
    vn
    @23
    cA
    @44
    vn
    @23
    nfcv
    nffv
    nffv
    @12
    @23
    wceq
    @13
    @24
    clog
    @12
    @23
    cA
    fveq2
    fveq2d
    cbvmpt
    eqtri
    elrnmpt
    ax-mp
    mpbir
    ne0ii
    @6
    @23
    cB
    cfv
    #
    cle
    wbr
    #
    vj
    cn
    wral
    #
    vx
    cr
    wrex
    #
    @10
    @21
    c1
    c4
    cdiv
    co
    #
    cmin
    co
    #
    cr
    wcel
    @53
    @48
    cle
    wbr
    #
    vj
    cn
    wral
    #
    @51
    @21
    @52
    @47
    c4
    4re
    4ne0
    rereccli
    resubcli
    @54
    vj
    cn
    cA
    cB
    vn
    vn
    cn
    c1
    @12
    @12
    c1
    caddc
    co
    cmul
    co
    cdiv
    co
    cmpt
    #
    @23
    stirlinglem13.1
    stirlinglem13.2
    @56
    eqid
    stirlinglem12
    rgen
    @50
    @55
    vx
    @53
    cr
    @6
    @53
    wceq
    @49
    @54
    vj
    cn
    @6
    @53
    @48
    cle
    breq1
    ralbidv
    rspcev
    mp2an
    #
    @50
    @9
    vx
    cr
    @50
    @8
    vy
    @0
    @50
    @11
    wa
    #
    @48
    @7
    wceq
    #
    vj
    cn
    wrex
    #
    @8
    @58
    @11
    @60
    @50
    @11
    simpr
    @19
    vn
    cn
    wral
    cB
    cn
    wfn
    @11
    @60
    wb
    @19
    vn
    cn
    @20
    rgen
    vn
    cn
    @14
    cB
    cr
    stirlinglem13.2
    fnmpt
    vj
    cn
    @7
    cB
    fvelrnb
    mp2b
    sylib
    @58
    @59
    @8
    vj
    cn
    @50
    @11
    vj
    @49
    vj
    cn
    nfra1
    @11
    vj
    nfv
    nfan
    @8
    vj
    nfv
    @58
    @23
    cn
    wcel
    #
    @59
    @8
    @58
    @61
    @59
    w3a
    #
    @6
    @48
    @7
    cle
    @62
    @50
    @61
    @49
    @50
    @11
    @61
    @59
    simp1l
    @58
    @61
    @59
    simp2
    @49
    vj
    cn
    rsp
    sylc
    @58
    @61
    @59
    simp3
    breqtrd
    3exp
    rexlimd
    mpd
    ralrimiva
    reximi
    ax-mp
    vx
    vy
    @0
    infrecl
    mp3an
    @3
    wtru
    vx
    vj
    cB
    c1
    cn
    nnuz
    wtru
    1zzd
    cn
    cr
    cB
    wf
    wtru
    vn
    cn
    cr
    @14
    cB
    stirlinglem13.2
    @20
    fmpti
    #
    a1i
    @61
    @23
    c1
    caddc
    co
    #
    cB
    cfv
    #
    @48
    cle
    wbr
    wtru
    @61
    @65
    @48
    @61
    @65
    @64
    cA
    cfv
    #
    clog
    cfv
    #
    cr
    @61
    @64
    cn
    wcel
    @67
    cr
    wcel
    @65
    @67
    wceq
    @23
    peano2nn
    #
    @61
    @66
    @61
    @66
    @64
    cfa
    cfv
    #
    c2
    @64
    cmul
    co
    #
    csqrt
    cfv
    #
    @64
    ceu
    cdiv
    co
    #
    @64
    cexp
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    crp
    @61
    vn
    @64
    @42
    @75
    cn
    cA
    cc
    cA
    @43
    wceq
    @61
    stirlinglem13.1
    a1i
    @61
    @12
    @64
    wceq
    #
    wa
    #
    @36
    @69
    @41
    @74
    cdiv
    @77
    @12
    @64
    cfa
    @61
    @76
    simpr
    #
    fveq2d
    @77
    @38
    @71
    @40
    @73
    cmul
    @77
    @37
    @70
    csqrt
    @77
    @12
    @64
    c2
    cmul
    @78
    oveq2d
    fveq2d
    @77
    @39
    @72
    @12
    @64
    cexp
    @77
    @12
    @64
    ceu
    cdiv
    @78
    oveq1d
    @78
    oveq12d
    oveq12d
    oveq12d
    @68
    @61
    @69
    @74
    @61
    @64
    cn0
    wcel
    #
    @69
    cn
    wcel
    #
    @69
    cc
    wcel
    @61
    @64
    @68
    nnnn0d
    #
    @64
    faccl
    #
    @69
    nncn
    3syl
    @61
    @71
    @73
    @61
    @70
    @61
    c2
    @64
    @61
    2cnd
    @61
    @23
    c1
    @23
    nncn
    @61
    1cnd
    addcld
    #
    mulcld
    sqrtcld
    #
    @61
    @72
    @64
    @61
    @64
    ceu
    @83
    ceu
    cc
    wcel
    @61
    ceu
    ere
    recni
    a1i
    #
    ceu
    cc0
    wne
    @61
    cc0
    ceu
    0re
    epos
    gtneii
    a1i
    #
    divcld
    #
    @81
    expcld
    #
    mulcld
    @61
    @71
    @73
    @84
    @88
    @61
    @71
    @61
    @70
    @61
    c2
    @64
    c2
    crp
    wcel
    @61
    2rp
    a1i
    @61
    @23
    @23
    nnre
    #
    @61
    cc0
    c1
    @23
    cc0
    cr
    wcel
    @61
    0re
    a1i
    @61
    1red
    @89
    cc0
    c1
    cle
    wbr
    @61
    0le1
    a1i
    @23
    nnge1
    letrd
    ge0p1rpd
    #
    rpmulcld
    #
    sqrtgt0d
    gt0ne0d
    @61
    @72
    @64
    @87
    @61
    @64
    ceu
    @83
    @85
    @61
    @64
    @68
    nnne0d
    @86
    divne0d
    @61
    @23
    @23
    nnz
    peano2zd
    #
    expne0d
    mulne0d
    divcld
    fvmptd
    @61
    @69
    @74
    @61
    @79
    @80
    @69
    crp
    wcel
    @81
    @82
    @69
    nnrp
    3syl
    @61
    @71
    @73
    @61
    @70
    @91
    rpsqrtcld
    @61
    @72
    @64
    @61
    @64
    ceu
    @90
    ceu
    crp
    wcel
    @61
    epr
    a1i
    rpdivcld
    @92
    rpexpcld
    rpmulcld
    rpdivcld
    eqeltrd
    relogcld
    #
    vn
    @64
    @14
    @67
    cn
    cB
    cr
    vn
    @64
    nfcv
    #
    vn
    @66
    clog
    @35
    vn
    @64
    cA
    @44
    @94
    nffv
    nffv
    @76
    @13
    @66
    clog
    @12
    @64
    cA
    fveq2
    fveq2d
    stirlinglem13.2
    fvmptf
    syl2anc
    @93
    eqeltrd
    cn
    cr
    @23
    cB
    @63
    ffvelrni
    cA
    cB
    vz
    vn
    vz
    cn
    c1
    c2
    vz
    cv
    cmul
    co
    #
    c1
    caddc
    co
    cdiv
    co
    c1
    c2
    @23
    cmul
    co
    c1
    caddc
    co
    cdiv
    co
    @95
    cexp
    co
    cmul
    co
    cmpt
    #
    @23
    stirlinglem13.1
    stirlinglem13.2
    @96
    eqid
    stirlinglem11
    ltled
    adantl
    @51
    wtru
    @57
    a1i
    climinf
    trud
    @5
    @3
    vd
    @1
    cr
    @4
    @1
    cB
    cli
    breq2
    rspcev
    mp2an
end
