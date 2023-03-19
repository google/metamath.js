include "cn.mm"
include "cv.mm"
include "cneg.mm"
include "cop.mm"
include "cmpt.mm"
include "cr.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "cico.mm"
include "cfv.mm"
include "ccom.mm"
include "cixp.mm"
include "ciun.mm"
include "wss.mm"
include "cpnf.mm"
include "cvol.mm"
include "cprod.mm"
include "csumge0.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wf.mm"
include "nnre.mm"
include "renegcld.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "ad2antlr.mm"
include "eqid.mm"
include "fmptd.mm"
include "wb.mm"
include "cvv.mm"
include "cfn.mm"
include "reex.mm"
include "xpex.mm"
include "a1i.mm"
include "elmapg.mm"
include "adantr.mm"
include "mpbird.mm"
include "ovex.mm"
include "nnex.mm"
include "elmap.mm"
include "sylibr.mm"
include "hoicvr.mm"
include "eqidd.mm"
include "cbvmptv.mm"
include "mpteq2i.mm"
include "fveq1d.mm"
include "coeq2d.mm"
include "ixpeq2dv.mm"
include "iuneq2d.mm"
include "sseqtrd.mm"
include "sstrd.mm"
include "c2.mm"
include "cmul.mm"
include "chash.mm"
include "cexp.mm"
include "c1st.mm"
include "c2nd.mm"
include "simpr.mm"
include "elexd.mm"
include "fvmpt2.mm"
include "fmpt3d.mm"
include "fvovco.mm"
include "opex.mm"
include "adantlr.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "negex.mm"
include "vex.mm"
include "op1st.mm"
include "op2nd.mm"
include "oveq12d.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cc0.mm"
include "cif.mm"
include "volico.mm"
include "crp.mm"
include "nnrp.mm"
include "neglt.mm"
include "syl.mm"
include "iftrued.mm"
include "caddc.mm"
include "recnd.mm"
include "subnegd.mm"
include "2timesd.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"
include "prodeq2dv.mm"
include "cc.mm"
include "2cnd.mm"
include "adantl.mm"
include "mulcld.mm"
include "fprodconst.mm"
include "mpteq2dva.mm"
include "cicc.mm"
include "cioo.mm"
include "ssriv.mm"
include "ioorp.mm"
include "eqcomi.mm"
include "sseqtri.mm"
include "ioossicc.mm"
include "sstri.mm"
include "cn0.mm"
include "2nn.mm"
include "nnmulcld.mm"
include "hashcl.mm"
include "nnexpcl.mm"
include "sseldi.mm"
include "sge0xrcl.mm"
include "c1.mm"
include "cxr.mm"
include "pnfxr.mm"
include "1nn.mm"
include "sselii.mm"
include "wn.mm"
include "nnnfi.mm"
include "1rp.mm"
include "sge0rpcpnf.mm"
include "eqcomd.mm"
include "xreqled.mm"
include "nfv.mm"
include "mptex2.mm"
include "nnge1d.mm"
include "sge0lempt.mm"
include "xrletrd.mm"
include "xrgepnfd.mm"
include "3eqtrrd.mm"
include "jca.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfeq.mm"
include "nfmpt.mm"
include "fveq1.mm"
include "ixpeq2d.mm"
include "iuneq2df.mm"
include "sseq2d.mm"
include "wral.mm"
include "a1d.mm"
include "ralrimi.mm"
include "prodeq2d.mm"
include "mpteq2da.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"

theorem hoicvrrex
  let wph: wff ph
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cX: class X
  let cY: class Y
  let vl: setvar l
  let vx: setvar x
  assume hoicvrrex.fi: |- ( ph -> X e. Fin )
  assume hoicvrrex.y: |- ( ph -> Y C_ ( RR ^m X ) )

  disjoint X i
  disjoint X j
  disjoint X k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint Y i
  disjoint j ph
  disjoint k ph
  disjoint X l
  disjoint j l
  disjoint k l
  disjoint l ph
  disjoint k x
  assert |- ( ph -> E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ( Y C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ +oo = ( sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) ) )

  proof
    wph
    vj
    cn
    vk
    cX
    vj
    cv
    #
    cneg
    #
    @0
    cop
    #
    cmpt
    #
    cmpt
    #
    cr
    cr
    cxp
    #
    cX
    cmap
    co
    #
    cn
    cmap
    co
    #
    wcel
    #
    cY
    vj
    cn
    vk
    cX
    vk
    cv
    #
    cico
    @0
    @4
    cfv
    #
    ccom
    #
    cfv
    #
    cixp
    #
    ciun
    #
    wss
    #
    cpnf
    vj
    cn
    cX
    @12
    cvol
    cfv
    #
    vk
    cprod
    #
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    cY
    vj
    cn
    vk
    cX
    @9
    cico
    @0
    vi
    cv
    #
    cfv
    #
    ccom
    #
    cfv
    #
    cixp
    #
    ciun
    #
    wss
    #
    cpnf
    vj
    cn
    cX
    @25
    cvol
    cfv
    #
    vk
    cprod
    #
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vi
    @7
    wrex
    wph
    cn
    @6
    @4
    wf
    @8
    wph
    vj
    cn
    @3
    @6
    @4
    wph
    @0
    cn
    wcel
    #
    wa
    #
    @3
    @6
    wcel
    #
    cX
    @5
    @3
    wf
    #
    @36
    vk
    cX
    @2
    @5
    @3
    @35
    @2
    @5
    wcel
    #
    wph
    @9
    cX
    wcel
    #
    @35
    @1
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    @39
    @35
    @0
    @0
    nnre
    #
    renegcld
    #
    @43
    @1
    @0
    cr
    cr
    opelxpi
    syl2anc
    ad2antlr
    #
    @3
    eqid
    #
    fmptd
    wph
    @37
    @38
    wb
    #
    @35
    wph
    @5
    cvv
    wcel
    #
    cX
    cfn
    wcel
    #
    @47
    @48
    wph
    cr
    cr
    reex
    reex
    xpex
    a1i
    hoicvrrex.fi
    @5
    cX
    @3
    cvv
    cfn
    elmapg
    syl2anc
    adantr
    mpbird
    #
    @4
    eqid
    #
    fmptd
    @6
    cn
    @4
    @5
    cX
    cmap
    ovex
    nnex
    elmap
    sylibr
    wph
    @15
    @20
    wph
    cY
    cr
    cX
    cmap
    co
    #
    @14
    hoicvrrex.y
    wph
    @52
    vj
    cn
    vk
    cX
    @9
    cico
    @0
    vj
    cn
    vl
    cX
    @2
    cmpt
    #
    cmpt
    #
    cfv
    #
    ccom
    #
    cfv
    #
    cixp
    #
    ciun
    @14
    wph
    vl
    vk
    vj
    @54
    cX
    @54
    eqid
    hoicvrrex.fi
    hoicvr
    wph
    vj
    cn
    @58
    @13
    wph
    vk
    cX
    @57
    @12
    wph
    @9
    @56
    @11
    wph
    @55
    @10
    cico
    wph
    @0
    @54
    @4
    @54
    @4
    wceq
    wph
    vj
    cn
    @53
    @3
    vl
    vk
    cX
    @2
    @2
    vl
    cv
    @9
    wceq
    @2
    eqidd
    cbvmptv
    mpteq2i
    a1i
    fveq1d
    coeq2d
    fveq1d
    ixpeq2dv
    iuneq2d
    sseqtrd
    sstrd
    wph
    @19
    vj
    cn
    c2
    @0
    cmul
    co
    #
    cX
    chash
    cfv
    #
    cexp
    co
    #
    cmpt
    #
    csumge0
    cfv
    #
    cpnf
    cpnf
    wph
    @18
    @62
    csumge0
    wph
    vj
    cn
    @17
    @61
    @36
    @17
    cX
    @59
    vk
    cprod
    #
    @61
    @36
    cX
    @16
    @59
    vk
    @36
    @40
    wa
    #
    @16
    @1
    @0
    cico
    co
    #
    cvol
    cfv
    #
    @59
    @65
    @12
    @66
    cvol
    @65
    @12
    @9
    @10
    cfv
    #
    c1st
    cfv
    #
    @68
    c2nd
    cfv
    #
    cico
    co
    @66
    @65
    @10
    cico
    cr
    cr
    cX
    @9
    @36
    cX
    @5
    @10
    wf
    @40
    @36
    vk
    cX
    @2
    @5
    @10
    @36
    @35
    @3
    cvv
    wcel
    @10
    @3
    wceq
    wph
    @35
    simpr
    #
    @36
    @3
    @6
    @50
    elexd
    vj
    cn
    @3
    cvv
    @4
    @51
    fvmpt2
    syl2anc
    #
    @45
    fmpt3d
    adantr
    @36
    @40
    simpr
    fvovco
    @65
    @69
    @1
    @70
    @0
    cico
    @65
    @69
    @2
    c1st
    cfv
    #
    @1
    @65
    @68
    @2
    c1st
    @65
    @68
    @9
    @3
    cfv
    #
    @2
    @36
    @68
    @74
    wceq
    @40
    @36
    @9
    @10
    @3
    @72
    fveq1d
    adantr
    wph
    @40
    @74
    @2
    wceq
    #
    @35
    wph
    @40
    wa
    #
    @40
    @2
    cvv
    wcel
    #
    @75
    wph
    @40
    simpr
    @77
    @76
    @1
    @0
    opex
    a1i
    vk
    cX
    @2
    cvv
    @3
    @46
    fvmpt2
    syl2anc
    adantlr
    eqtrd
    #
    fveq2d
    @73
    @1
    wceq
    @65
    @1
    @0
    @0
    negex
    #
    vj
    vex
    #
    op1st
    a1i
    eqtrd
    @65
    @70
    @2
    c2nd
    cfv
    #
    @0
    @65
    @68
    @2
    c2nd
    @78
    fveq2d
    @81
    @0
    wceq
    @65
    @1
    @0
    @79
    @80
    op2nd
    a1i
    eqtrd
    oveq12d
    eqtrd
    fveq2d
    @35
    @67
    @59
    wceq
    wph
    @40
    @35
    @67
    @1
    @0
    clt
    wbr
    #
    @0
    @1
    cmin
    co
    #
    cc0
    cif
    #
    @83
    @59
    @35
    @41
    @42
    @67
    @84
    wceq
    @44
    @43
    @1
    @0
    volico
    syl2anc
    @35
    @82
    @83
    cc0
    @35
    @0
    crp
    wcel
    @82
    @0
    nnrp
    #
    @0
    neglt
    syl
    iftrued
    @35
    @83
    @0
    @0
    caddc
    co
    @59
    @35
    @0
    @0
    @35
    @0
    @43
    recnd
    #
    @86
    subnegd
    @35
    @0
    @86
    2timesd
    eqtr4d
    3eqtrd
    ad2antlr
    eqtrd
    prodeq2dv
    @36
    @49
    @59
    cc
    wcel
    @64
    @61
    wceq
    wph
    @49
    @35
    hoicvrrex.fi
    adantr
    @36
    c2
    @0
    @36
    2cnd
    @35
    @0
    cc
    wcel
    wph
    @86
    adantl
    mulcld
    cX
    @59
    vk
    fprodconst
    syl2anc
    eqtrd
    mpteq2dva
    fveq2d
    wph
    @63
    wph
    @62
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
    vj
    cn
    @61
    cc0
    cpnf
    cicc
    co
    #
    @62
    @36
    cn
    @88
    @61
    cn
    cc0
    cpnf
    cioo
    co
    #
    @88
    cn
    crp
    @89
    vj
    cn
    crp
    @85
    ssriv
    @89
    crp
    ioorp
    eqcomi
    sseqtri
    cc0
    cpnf
    ioossicc
    sstri
    #
    @36
    @59
    cn
    wcel
    @60
    cn0
    wcel
    #
    @61
    cn
    wcel
    @36
    c2
    @0
    c2
    cn
    wcel
    @36
    2nn
    a1i
    @71
    nnmulcld
    wph
    @91
    @35
    wph
    @49
    @91
    hoicvrrex.fi
    cX
    hashcl
    syl
    adantr
    @59
    @60
    nnexpcl
    syl2anc
    #
    sseldi
    #
    @62
    eqid
    fmptd
    sge0xrcl
    #
    wph
    cpnf
    vj
    cn
    c1
    cmpt
    #
    csumge0
    cfv
    #
    @63
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    #
    wph
    @95
    cvv
    cn
    @87
    wph
    vj
    cn
    c1
    @88
    @95
    c1
    @88
    wcel
    @36
    cn
    @88
    c1
    @90
    1nn
    sselii
    a1i
    @95
    eqid
    fmptd
    #
    sge0xrcl
    @94
    wph
    cpnf
    @96
    @97
    wph
    @96
    cpnf
    wph
    vj
    cn
    c1
    cvv
    @87
    cn
    cfn
    wcel
    wn
    wph
    nnnfi
    a1i
    c1
    crp
    wcel
    wph
    1rp
    a1i
    sge0rpcpnf
    eqcomd
    xreqled
    wph
    vj
    cn
    c1
    @61
    cvv
    wph
    vj
    nfv
    @87
    wph
    vj
    cn
    c1
    @88
    @98
    mptex2
    @93
    @36
    @61
    @92
    nnge1d
    sge0lempt
    xrletrd
    xrgepnfd
    wph
    cpnf
    eqidd
    3eqtrrd
    jca
    @34
    @21
    vi
    @4
    @7
    @22
    @4
    wceq
    #
    @28
    @15
    @33
    @20
    @99
    @27
    @14
    cY
    @99
    vj
    cn
    @26
    @13
    vj
    @22
    @4
    vj
    @22
    nfcv
    vj
    cn
    @3
    nfmpt1
    nfeq
    #
    @99
    @26
    @13
    wceq
    @35
    @99
    vk
    cX
    @25
    @12
    vk
    @22
    @4
    vk
    @22
    nfcv
    vk
    vj
    cn
    @3
    vk
    cn
    nfcv
    vk
    cX
    @2
    nfmpt1
    nfmpt
    nfeq
    #
    @99
    @25
    @12
    wceq
    @40
    @99
    @9
    @24
    @11
    @99
    @23
    @10
    cico
    @0
    @22
    @4
    fveq1
    coeq2d
    fveq1d
    #
    adantr
    ixpeq2d
    adantr
    iuneq2df
    sseq2d
    @99
    @32
    @19
    cpnf
    @99
    @31
    @18
    csumge0
    @99
    vj
    cn
    @30
    @17
    @100
    @99
    @35
    wa
    cX
    @29
    @16
    vk
    @99
    @29
    @16
    wceq
    #
    vk
    cX
    wral
    @35
    @99
    @103
    vk
    cX
    @101
    @99
    @103
    @40
    @99
    @25
    @12
    cvol
    @102
    fveq2d
    a1d
    ralrimi
    adantr
    prodeq2d
    mpteq2da
    fveq2d
    eqeq2d
    anbi12d
    rspcev
    syl2anc
end
