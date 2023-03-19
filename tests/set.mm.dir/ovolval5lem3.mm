include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "wceq.mm"
include "wtru.mm"
include "wss.mm"
include "wcel.mm"
include "cioo.mm"
include "cv.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "cvol.mm"
include "csumge0.mm"
include "cfv.mm"
include "wa.mm"
include "cr.mm"
include "cxp.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "infxrcl.mm"
include "mp1i.mm"
include "cico.mm"
include "a1i.mm"
include "crp.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "simpr.mm"
include "rabeq2i.mm"
include "biimpi.mm"
include "simprd.mm"
include "adantr.mm"
include "w3a.mm"
include "c1st.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "cmin.mm"
include "c2nd.mm"
include "cop.mm"
include "cmpt.mm"
include "coeq2.mm"
include "rneqd.mm"
include "unieqd.mm"
include "sseq2d.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "rabbii.mm"
include "eqtr4i.mm"
include "simp3r.mm"
include "eqid.mm"
include "wf.mm"
include "elmapi.mm"
include "3ad2ant2.mm"
include "simp3l.mm"
include "simp1.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "opeq12d.mm"
include "cbvmptv.mm"
include "ovolval5lem2.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "imp.mm"
include "syl2anc.mm"
include "3adant1.mm"
include "infleinf.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "cbvrabv.mm"
include "wi.mm"
include "wral.mm"
include "ciun.mm"
include "ioossico.mm"
include "fvovco.mm"
include "sseq12d.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "ss2iun.mm"
include "syl.mm"
include "wfn.mm"
include "cpw.mm"
include "ioof.mm"
include "rexpssxrxp.mm"
include "fssd.mm"
include "fco.mm"
include "ffn.mm"
include "fniunfv.mm"
include "icof.mm"
include "mpbid.mm"
include "sstrd.mm"
include "adantrr.mm"
include "voliooicof.mm"
include "eqtrd.mm"
include "adantrl.mm"
include "jca.mm"
include "ex.mm"
include "reximia.mm"
include "rgenw.mm"
include "ss2rab.mm"
include "mpbir.mm"
include "sseq12i.mm"
include "infxrss.mm"
include "mp2an.mm"
include "xrletrid.mm"
include "trud.mm"

theorem ovolval5lem3
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cQ: class Q
  let vf: setvar f
  let cM: class M
  let vg: setvar g
  let vn: setvar n
  let vw: setvar w
  let vm: setvar m
  let vk: setvar k
  let vx: setvar x
  assume ovolval5lem3.m: |- M = { y e. RR* | E. f e. ( ( RR X. RR ) ^m NN ) ( A C_ U. ran ( [,) o. f ) /\ y = ( sum^ ` ( ( vol o. [,) ) o. f ) ) ) }
  assume ovolval5lem3.q: |- Q = { z e. RR* | E. f e. ( ( RR X. RR ) ^m NN ) ( A C_ U. ran ( (,) o. f ) /\ z = ( sum^ ` ( ( vol o. (,) ) o. f ) ) ) }

  disjoint A f
  disjoint A z
  disjoint f z
  disjoint A y
  disjoint f y
  disjoint M y
  disjoint M z
  disjoint y z
  disjoint Q f
  disjoint Q y
  disjoint Q z
  disjoint A g
  disjoint f g
  disjoint g z
  disjoint A n
  disjoint f n
  disjoint n y
  disjoint M w
  disjoint w y
  disjoint w z
  disjoint Q w
  disjoint f w
  disjoint f m
  disjoint g m
  disjoint g w
  disjoint m w
  disjoint m z
  disjoint m n
  disjoint n w
  disjoint k x
  assert |- inf ( Q , RR* , < ) = inf ( M , RR* , < )

  proof
    cQ
    cxr
    clt
    cinf
    #
    cM
    cxr
    clt
    cinf
    #
    wceq
    wtru
    @0
    @1
    cQ
    cxr
    wss
    #
    @0
    cxr
    wcel
    wtru
    cQ
    cA
    cioo
    vf
    cv
    #
    ccom
    #
    crn
    #
    cuni
    #
    wss
    #
    vz
    cv
    #
    cvol
    cioo
    ccom
    #
    @3
    ccom
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vf
    cr
    cr
    cxp
    #
    cn
    cmap
    co
    #
    wrex
    #
    vz
    cxr
    crab
    #
    cxr
    ovolval5lem3.q
    @16
    vz
    cxr
    ssrab2
    eqsstri
    #
    cQ
    infxrcl
    mp1i
    cM
    cxr
    wss
    #
    @1
    cxr
    wcel
    wtru
    cM
    cA
    cico
    @3
    ccom
    #
    crn
    cuni
    #
    wss
    #
    vy
    cv
    #
    cvol
    cico
    ccom
    @3
    ccom
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vf
    @15
    wrex
    #
    vy
    cxr
    crab
    #
    cxr
    ovolval5lem3.m
    @28
    vy
    cxr
    ssrab2
    eqsstri
    #
    cM
    infxrcl
    mp1i
    wtru
    vy
    vw
    vz
    cQ
    cM
    @2
    wtru
    @18
    a1i
    @19
    wtru
    @30
    a1i
    @23
    cM
    wcel
    #
    vw
    cv
    #
    crp
    wcel
    #
    @8
    @23
    @32
    cxad
    co
    cle
    wbr
    vz
    cQ
    wrex
    #
    wtru
    @31
    @33
    wa
    @33
    @28
    @34
    @31
    @33
    simpr
    @31
    @28
    @33
    @31
    @23
    cxr
    wcel
    #
    @28
    @31
    @35
    @28
    wa
    @28
    vy
    cM
    cxr
    ovolval5lem3.m
    rabeq2i
    biimpi
    simprd
    adantr
    @33
    @28
    @34
    @33
    @27
    @34
    vf
    @15
    @33
    @3
    @15
    wcel
    #
    @27
    @34
    @33
    @36
    @27
    w3a
    vz
    cA
    cQ
    vg
    vn
    @3
    vm
    cn
    vm
    cv
    #
    @3
    cfv
    #
    c1st
    cfv
    #
    @32
    c2
    @37
    cexp
    co
    #
    cdiv
    co
    #
    cmin
    co
    #
    @38
    c2nd
    cfv
    #
    cop
    #
    cmpt
    #
    @32
    @23
    @9
    @45
    ccom
    csumge0
    cfv
    #
    cQ
    @17
    cA
    cioo
    vg
    cv
    #
    ccom
    #
    crn
    #
    cuni
    #
    wss
    #
    @8
    @9
    @47
    ccom
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vg
    @15
    wrex
    #
    vz
    cxr
    crab
    ovolval5lem3.q
    @56
    @16
    vz
    cxr
    @55
    @13
    vg
    vf
    @15
    @47
    @3
    wceq
    #
    @51
    @7
    @54
    @12
    @57
    @50
    @6
    cA
    @57
    @49
    @5
    @57
    @48
    @4
    @47
    @3
    cioo
    coeq2
    rneqd
    unieqd
    sseq2d
    @57
    @53
    @11
    @8
    @57
    @52
    @10
    csumge0
    @47
    @3
    @9
    coeq2
    fveq2d
    eqeq2d
    anbi12d
    cbvrexv
    rabbii
    eqtr4i
    @33
    @36
    @22
    @26
    simp3r
    @46
    eqid
    @36
    @33
    cn
    @14
    @3
    wf
    #
    @27
    @3
    @14
    cn
    elmapi
    #
    3ad2ant2
    @33
    @36
    @22
    @26
    simp3l
    @33
    @36
    @27
    simp1
    vm
    vn
    cn
    @44
    vn
    cv
    #
    @3
    cfv
    #
    c1st
    cfv
    #
    @32
    c2
    @60
    cexp
    co
    #
    cdiv
    co
    #
    cmin
    co
    #
    @61
    c2nd
    cfv
    #
    cop
    @37
    @60
    wceq
    #
    @42
    @65
    @43
    @66
    @67
    @39
    @62
    @41
    @64
    cmin
    @67
    @38
    @61
    c1st
    @37
    @60
    @3
    fveq2
    #
    fveq2d
    @67
    @40
    @63
    @32
    cdiv
    @37
    @60
    c2
    cexp
    oveq2
    oveq2d
    oveq12d
    @67
    @38
    @61
    c2nd
    @68
    fveq2d
    opeq12d
    cbvmptv
    ovolval5lem2
    3exp
    rexlimdv
    imp
    syl2anc
    3adant1
    infleinf
    @1
    @0
    cle
    wbr
    #
    wtru
    cQ
    cM
    wss
    #
    @19
    @69
    @70
    @17
    @29
    wss
    @17
    @7
    @23
    @11
    wceq
    #
    wa
    #
    vf
    @15
    wrex
    #
    vy
    cxr
    crab
    #
    @29
    @16
    @73
    vz
    vy
    cxr
    @8
    @23
    wceq
    #
    @13
    @72
    vf
    @15
    @75
    @12
    @71
    @7
    @8
    @23
    @11
    eqeq1
    anbi2d
    rexbidv
    cbvrabv
    @74
    @29
    wss
    @73
    @28
    wi
    #
    vy
    cxr
    wral
    @76
    vy
    cxr
    @72
    @27
    vf
    @15
    @36
    @72
    @27
    @36
    @72
    wa
    @22
    @26
    @36
    @7
    @22
    @71
    @36
    @7
    wa
    cA
    @6
    @21
    @36
    @7
    simpr
    @36
    @6
    @21
    wss
    #
    @7
    @36
    vn
    cn
    @60
    @4
    cfv
    #
    ciun
    #
    vn
    cn
    @60
    @20
    cfv
    #
    ciun
    #
    wss
    #
    @77
    @36
    @78
    @80
    wss
    #
    vn
    cn
    wral
    @82
    @36
    @83
    vn
    cn
    @36
    @60
    cn
    wcel
    #
    wa
    #
    @83
    @62
    @66
    cioo
    co
    #
    @62
    @66
    cico
    co
    #
    wss
    #
    @88
    @85
    @62
    @66
    ioossico
    a1i
    @85
    @78
    @86
    @80
    @87
    @85
    @3
    cioo
    cr
    cr
    cn
    @60
    @36
    @58
    @84
    @59
    adantr
    #
    @36
    @84
    simpr
    #
    fvovco
    @85
    @3
    cico
    cr
    cr
    cn
    @60
    @89
    @90
    fvovco
    sseq12d
    mpbird
    ralrimiva
    vn
    cn
    @78
    @80
    ss2iun
    syl
    @36
    @79
    @6
    @81
    @21
    @36
    @4
    cn
    wfn
    #
    @79
    @6
    wceq
    @36
    cn
    cr
    cpw
    #
    @4
    wf
    #
    @91
    @36
    cxr
    cxr
    cxp
    #
    @92
    cioo
    wf
    #
    cn
    @94
    @3
    wf
    #
    @93
    @95
    @36
    ioof
    a1i
    @36
    cn
    @14
    @94
    @3
    @59
    @14
    @94
    wss
    @36
    rexpssxrxp
    a1i
    fssd
    #
    cn
    @94
    @92
    cioo
    @3
    fco
    syl2anc
    cn
    @92
    @4
    ffn
    syl
    vn
    cn
    @4
    fniunfv
    syl
    @36
    @20
    cn
    wfn
    #
    @81
    @21
    wceq
    @36
    cn
    cxr
    cpw
    #
    @20
    wf
    #
    @98
    @36
    @94
    @99
    cico
    wf
    #
    @96
    @100
    @101
    @36
    icof
    a1i
    @97
    cn
    @94
    @99
    cico
    @3
    fco
    syl2anc
    cn
    @99
    @20
    ffn
    syl
    vn
    cn
    @20
    fniunfv
    syl
    sseq12d
    mpbid
    adantr
    sstrd
    adantrr
    @36
    @71
    @26
    @7
    @36
    @71
    wa
    @23
    @11
    @25
    @36
    @71
    simpr
    @36
    @11
    @25
    wceq
    @71
    @36
    @10
    @24
    csumge0
    @36
    cn
    @3
    @59
    voliooicof
    fveq2d
    adantr
    eqtrd
    adantrl
    jca
    ex
    reximia
    rgenw
    @73
    @28
    vy
    cxr
    ss2rab
    mpbir
    eqsstri
    cQ
    @17
    cM
    @29
    ovolval5lem3.q
    ovolval5lem3.m
    sseq12i
    mpbir
    @30
    cQ
    cM
    infxrss
    mp2an
    a1i
    xrletrid
    trud
end
