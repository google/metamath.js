include "wcel.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "cxr.mm"
include "cioo.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "cvol.mm"
include "csumge0.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cr.mm"
include "cxp.mm"
include "cn.mm"
include "cmap.mm"
include "a1i.mm"
include "cvv.mm"
include "nnex.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wf.mm"
include "volioof.mm"
include "rexpssxrxp.mm"
include "c1st.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "cmin.mm"
include "c2nd.mm"
include "cop.mm"
include "ffvelrnda.mm"
include "xp1st.mm"
include "syl.mm"
include "rpred.mm"
include "adantr.mm"
include "2nn.mm"
include "nnnn0.mm"
include "nnexpcld.mm"
include "nnred.mm"
include "adantl.mm"
include "wne.mm"
include "nnne0d.mm"
include "redivcld.mm"
include "resubcld.mm"
include "xp2nd.mm"
include "opelxpd.mm"
include "fmptd.mm"
include "fcoss.mm"
include "sge0xrcl.mm"
include "eqeltrd.mm"
include "reex.mm"
include "xpex.mm"
include "elmapd.mm"
include "mpbird.mm"
include "cico.mm"
include "ciun.mm"
include "wral.mm"
include "clt.mm"
include "rexrd.mm"
include "crp.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "ltsubrpd.mm"
include "id.mm"
include "opex.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "ovex.mm"
include "fvex.mm"
include "op1stg.mm"
include "mp2an.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "op2nd.mm"
include "eqcomd.mm"
include "eqled.mm"
include "icossioo.mm"
include "syl22anc.mm"
include "1st2nd2.mm"
include "df-ov.mm"
include "eqtr4d.mm"
include "sseq12d.mm"
include "ralrimiva.mm"
include "ss2iun.mm"
include "cmpt.mm"
include "rgenw.mm"
include "dfiun3g.mm"
include "cpw.mm"
include "icof.mm"
include "fcomptss.mm"
include "rneqd.mm"
include "unieqd.mm"
include "eqtr2d.mm"
include "ioof.mm"
include "sstrd.mm"
include "jca.mm"
include "coeq2.mm"
include "sseq2d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "sylibr.mm"
include "crab.mm"
include "fveq2.mm"
include "breq12d.mm"
include "cbvrabv.mm"
include "ovolval5lem1.mm"
include "nfcv.mm"
include "fssd.mm"
include "volioofmpt.mm"
include "oveq12d.mm"
include "mpteq2dva.mm"
include "ressxr.mm"
include "xpss2.mm"
include "ax-mp.mm"
include "volicofmpt.mm"
include "oveq1d.mm"
include "breq1.mm"

theorem ovolval5lem2
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cQ: class Q
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vm: setvar m
  let vk: setvar k
  let vx: setvar x
  assume ovolval5lem2.q: |- Q = { z e. RR* | E. f e. ( ( RR X. RR ) ^m NN ) ( A C_ U. ran ( (,) o. f ) /\ z = ( sum^ ` ( ( vol o. (,) ) o. f ) ) ) }
  assume ovolval5lem2.y: |- ( ph -> Y = ( sum^ ` ( ( vol o. [,) ) o. F ) ) )
  assume ovolval5lem2.z: |- Z = ( sum^ ` ( ( vol o. (,) ) o. G ) )
  assume ovolval5lem2.f: |- ( ph -> F : NN --> ( RR X. RR ) )
  assume ovolval5lem2.s: |- ( ph -> A C_ U. ran ( [,) o. F ) )
  assume ovolval5lem2.w: |- ( ph -> W e. RR+ )
  assume ovolval5lem2.g: |- G = ( n e. NN |-> <. ( ( 1st ` ( F ` n ) ) - ( W / ( 2 ^ n ) ) ) , ( 2nd ` ( F ` n ) ) >. )

  disjoint A f
  disjoint A z
  disjoint f z
  disjoint F n
  disjoint G f
  disjoint G n
  disjoint Q z
  disjoint W n
  disjoint W z
  disjoint Y z
  disjoint Z f
  disjoint Z z
  disjoint n ph
  disjoint F m
  disjoint m n
  disjoint k x
  assert |- ( ph -> E. z e. Q z <_ ( Y +e W ) )

  proof
    wph
    cZ
    cQ
    wcel
    #
    cZ
    cY
    cW
    cxad
    co
    #
    cle
    wbr
    #
    vz
    cv
    #
    @1
    cle
    wbr
    #
    vz
    cQ
    wrex
    wph
    cZ
    cxr
    wcel
    #
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
    cZ
    cvol
    cioo
    ccom
    #
    @6
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
    wa
    @0
    wph
    @5
    @18
    wph
    cZ
    @11
    cG
    ccom
    #
    csumge0
    cfv
    #
    cxr
    cZ
    @20
    wceq
    #
    wph
    ovolval5lem2.z
    a1i
    #
    wph
    @19
    cvv
    cn
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    #
    wph
    cxr
    cxr
    cxp
    #
    cc0
    cpnf
    cicc
    co
    #
    @16
    cn
    @11
    cG
    @24
    @25
    @11
    wf
    wph
    volioof
    a1i
    @16
    @24
    wss
    wph
    rexpssxrxp
    a1i
    #
    wph
    vn
    cn
    vn
    cv
    #
    cF
    cfv
    #
    c1st
    cfv
    #
    cW
    c2
    @27
    cexp
    co
    #
    cdiv
    co
    #
    cmin
    co
    #
    @28
    c2nd
    cfv
    #
    cop
    #
    @16
    cG
    wph
    @27
    cn
    wcel
    #
    wa
    #
    @32
    @33
    cr
    cr
    @36
    @29
    @31
    @36
    @28
    @16
    wcel
    #
    @29
    cr
    wcel
    wph
    cn
    @16
    @27
    cF
    ovolval5lem2.f
    ffvelrnda
    #
    @28
    cr
    cr
    xp1st
    syl
    #
    @36
    cW
    @30
    wph
    cW
    cr
    wcel
    @35
    wph
    cW
    ovolval5lem2.w
    rpred
    adantr
    @35
    @30
    cr
    wcel
    wph
    @35
    @30
    @35
    c2
    @27
    c2
    cn
    wcel
    @35
    2nn
    a1i
    @27
    nnnn0
    nnexpcld
    #
    nnred
    adantl
    @35
    @30
    cc0
    wne
    wph
    @35
    @30
    @40
    nnne0d
    adantl
    redivcld
    resubcld
    @36
    @37
    @33
    cr
    wcel
    @38
    @28
    cr
    cr
    xp2nd
    syl
    #
    opelxpd
    ovolval5lem2.g
    fmptd
    #
    fcoss
    sge0xrcl
    eqeltrd
    wph
    cG
    @17
    wcel
    #
    cA
    cioo
    cG
    ccom
    #
    crn
    #
    cuni
    #
    wss
    #
    @21
    wa
    #
    @18
    wph
    @43
    cn
    @16
    cG
    wf
    @42
    wph
    @16
    cn
    cG
    cvv
    cvv
    @16
    cvv
    wcel
    wph
    cr
    cr
    reex
    reex
    xpex
    a1i
    @23
    elmapd
    mpbird
    wph
    @47
    @21
    wph
    cA
    cico
    cF
    ccom
    #
    crn
    #
    cuni
    #
    @46
    ovolval5lem2.s
    wph
    @51
    @46
    wss
    vn
    cn
    @28
    cico
    cfv
    #
    ciun
    #
    vn
    cn
    @27
    cG
    cfv
    #
    cioo
    cfv
    #
    ciun
    #
    wss
    #
    wph
    @52
    @55
    wss
    #
    vn
    cn
    wral
    @57
    wph
    @58
    vn
    cn
    @36
    @58
    @29
    @33
    cico
    co
    #
    @54
    c1st
    cfv
    #
    @54
    c2nd
    cfv
    #
    cioo
    co
    #
    wss
    #
    @36
    @60
    cxr
    wcel
    @61
    cxr
    wcel
    @60
    @29
    clt
    wbr
    #
    @33
    @61
    cle
    wbr
    @63
    @36
    @60
    @36
    @54
    @16
    wcel
    #
    @60
    cr
    wcel
    wph
    cn
    @16
    @27
    cG
    @42
    ffvelrnda
    #
    @54
    cr
    cr
    xp1st
    syl
    rexrd
    @36
    @61
    @36
    @65
    @61
    cr
    wcel
    @66
    @54
    cr
    cr
    xp2nd
    syl
    rexrd
    @36
    @64
    @32
    @29
    clt
    wbr
    @36
    @29
    @31
    @39
    @36
    cW
    @30
    wph
    cW
    crp
    wcel
    @35
    ovolval5lem2.w
    adantr
    @35
    @30
    crp
    wcel
    wph
    @35
    @30
    @40
    nnrpd
    adantl
    rpdivcld
    ltsubrpd
    @36
    @60
    @32
    @29
    clt
    @35
    @60
    @32
    wceq
    wph
    @35
    @60
    @34
    c1st
    cfv
    #
    @32
    @35
    @54
    @34
    c1st
    @35
    @35
    @34
    cvv
    wcel
    #
    @54
    @34
    wceq
    @35
    id
    @68
    @35
    @32
    @33
    opex
    a1i
    vn
    cn
    @34
    cvv
    cG
    ovolval5lem2.g
    fvmpt2
    syl2anc
    #
    fveq2d
    @67
    @32
    wceq
    #
    @35
    @32
    cvv
    wcel
    @33
    cvv
    wcel
    @70
    @29
    @31
    cmin
    ovex
    #
    @28
    c2nd
    fvex
    #
    @32
    @33
    cvv
    cvv
    op1stg
    mp2an
    a1i
    eqtrd
    adantl
    #
    breq1d
    mpbird
    @36
    @33
    @61
    @41
    @36
    @61
    @33
    @35
    @61
    @33
    wceq
    wph
    @35
    @61
    @34
    c2nd
    cfv
    #
    @33
    @35
    @54
    @34
    c2nd
    @69
    fveq2d
    @74
    @33
    wceq
    @35
    @32
    @33
    @71
    @72
    op2nd
    a1i
    eqtrd
    adantl
    #
    eqcomd
    eqled
    @60
    @61
    @29
    @33
    icossioo
    syl22anc
    @36
    @52
    @59
    @55
    @62
    @36
    @52
    @29
    @33
    cop
    #
    cico
    cfv
    #
    @59
    @36
    @28
    @76
    cico
    @36
    @37
    @28
    @76
    wceq
    @38
    @28
    cr
    cr
    1st2nd2
    syl
    fveq2d
    @59
    @77
    wceq
    @36
    @29
    @33
    cico
    df-ov
    a1i
    eqtr4d
    @36
    @55
    @60
    @61
    cop
    #
    cioo
    cfv
    #
    @62
    @36
    @54
    @78
    cioo
    @36
    @65
    @54
    @78
    wceq
    @66
    @54
    cr
    cr
    1st2nd2
    syl
    fveq2d
    @62
    @79
    wceq
    @36
    @60
    @61
    cioo
    df-ov
    a1i
    eqtr4d
    sseq12d
    mpbird
    ralrimiva
    vn
    cn
    @52
    @55
    ss2iun
    syl
    wph
    @51
    @53
    @46
    @56
    wph
    @53
    vn
    cn
    @52
    cmpt
    #
    crn
    #
    cuni
    #
    @51
    wph
    @52
    cvv
    wcel
    #
    vn
    cn
    wral
    #
    @53
    @82
    wceq
    @84
    wph
    @83
    vn
    cn
    @28
    cico
    fvex
    rgenw
    a1i
    vn
    cn
    @52
    cvv
    dfiun3g
    syl
    wph
    @81
    @50
    wph
    @80
    @49
    wph
    @49
    @80
    wph
    vn
    cn
    @16
    @24
    cxr
    cpw
    #
    cF
    cico
    ovolval5lem2.f
    @26
    @24
    @85
    cico
    wf
    wph
    icof
    a1i
    fcomptss
    eqcomd
    rneqd
    unieqd
    eqtr2d
    wph
    @56
    vn
    cn
    @55
    cmpt
    #
    crn
    #
    cuni
    #
    @46
    wph
    @55
    cvv
    wcel
    #
    vn
    cn
    wral
    #
    @56
    @88
    wceq
    @90
    wph
    @89
    vn
    cn
    @54
    cioo
    fvex
    rgenw
    a1i
    vn
    cn
    @55
    cvv
    dfiun3g
    syl
    wph
    @87
    @45
    wph
    @86
    @44
    wph
    @44
    @86
    wph
    vn
    cn
    @16
    @24
    cr
    cpw
    #
    cG
    cioo
    @42
    @26
    @24
    @91
    cioo
    wf
    wph
    ioof
    a1i
    fcomptss
    eqcomd
    rneqd
    unieqd
    eqtr2d
    sseq12d
    mpbird
    sstrd
    @22
    jca
    @15
    @48
    vf
    cG
    @17
    @6
    cG
    wceq
    #
    @10
    @47
    @14
    @21
    @92
    @9
    @46
    cA
    @92
    @8
    @45
    @92
    @7
    @44
    @6
    cG
    cioo
    coeq2
    rneqd
    unieqd
    sseq2d
    @92
    @13
    @20
    cZ
    @92
    @12
    @19
    csumge0
    @6
    cG
    @11
    coeq2
    fveq2d
    eqeq2d
    anbi12d
    rspcev
    syl2anc
    jca
    @10
    @3
    @13
    wceq
    #
    wa
    #
    vf
    @17
    wrex
    @18
    vz
    cZ
    cxr
    cQ
    @3
    cZ
    wceq
    #
    @94
    @15
    vf
    @17
    @95
    @93
    @14
    @10
    @3
    cZ
    @13
    eqeq1
    anbi2d
    rexbidv
    ovolval5lem2.q
    elrab2
    sylibr
    wph
    @2
    vn
    cn
    @32
    @33
    cioo
    co
    #
    cvol
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    vn
    cn
    @59
    cvol
    cfv
    cmpt
    #
    csumge0
    cfv
    #
    cW
    cxad
    co
    #
    cle
    wbr
    wph
    @29
    @33
    vm
    cv
    #
    cF
    cfv
    #
    c1st
    cfv
    #
    @104
    c2nd
    cfv
    #
    clt
    wbr
    #
    vm
    cn
    crab
    vn
    cW
    @39
    @41
    ovolval5lem2.w
    @107
    @29
    @33
    clt
    wbr
    vm
    vn
    cn
    @103
    @27
    wceq
    #
    @105
    @29
    @106
    @33
    clt
    @108
    @104
    @28
    c1st
    @103
    @27
    cF
    fveq2
    #
    fveq2d
    @108
    @104
    @28
    c2nd
    @109
    fveq2d
    breq12d
    cbvrabv
    ovolval5lem1
    wph
    cZ
    @99
    @1
    @102
    cle
    wph
    cZ
    @20
    @99
    @22
    wph
    @19
    @98
    csumge0
    wph
    @19
    vn
    cn
    @62
    cvol
    cfv
    #
    cmpt
    @98
    wph
    vn
    cn
    cG
    vn
    cG
    nfcv
    wph
    cn
    @16
    @24
    cG
    @42
    @26
    fssd
    volioofmpt
    wph
    vn
    cn
    @110
    @97
    @36
    @62
    @96
    cvol
    @36
    @60
    @32
    @61
    @33
    cioo
    @73
    @75
    oveq12d
    fveq2d
    mpteq2dva
    eqtrd
    fveq2d
    eqtrd
    wph
    cY
    @101
    cW
    cxad
    wph
    cY
    cvol
    cico
    ccom
    cF
    ccom
    #
    csumge0
    cfv
    @101
    ovolval5lem2.y
    wph
    @111
    @100
    csumge0
    wph
    vn
    cn
    cF
    vn
    cF
    nfcv
    wph
    cn
    @16
    cr
    cxr
    cxp
    #
    cF
    ovolval5lem2.f
    @16
    @112
    wss
    #
    wph
    cr
    cxr
    wss
    @113
    ressxr
    cr
    cxr
    cr
    xpss2
    ax-mp
    a1i
    fssd
    volicofmpt
    fveq2d
    eqtrd
    oveq1d
    breq12d
    mpbird
    @4
    @2
    vz
    cZ
    cQ
    @3
    cZ
    @1
    cle
    breq1
    rspcev
    syl2anc
end
