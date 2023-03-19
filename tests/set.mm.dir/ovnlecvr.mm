include "covoln.mm"
include "cfv.mm"
include "cn.mm"
include "cv.mm"
include "cico.mm"
include "ccom.mm"
include "cixp.mm"
include "ciun.mm"
include "wss.mm"
include "cvol.mm"
include "cprod.mm"
include "cmpt.mm"
include "csumge0.mm"
include "wceq.mm"
include "wa.mm"
include "cr.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "cxr.mm"
include "crab.mm"
include "clt.mm"
include "cinf.mm"
include "cle.mm"
include "wral.mm"
include "wcel.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "elmapi.mm"
include "syl.mm"
include "hoissrrn.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "sstrd.mm"
include "eqid.mm"
include "ovnn0val.mm"
include "wbr.mm"
include "ssrab2.mm"
include "a1i.mm"
include "cvv.mm"
include "nnex.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "icossicc.mm"
include "nfv.mm"
include "cfn.mm"
include "adantr.mm"
include "hoiprodcl2.mm"
include "sseldi.mm"
include "fmptd.mm"
include "sge0xrcl.mm"
include "wb.mm"
include "ovex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "ax-mp.mm"
include "coeq2.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "prodeq2ad.mm"
include "adantl.mm"
include "prodex.mm"
include "fvmptd.mm"
include "mpteq2dva.mm"
include "jca.mm"
include "fveq1.mm"
include "coeq2d.mm"
include "ixpeq2d.mm"
include "iuneq2d.mm"
include "sseq2d.mm"
include "mpteq2dv.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "infxrlb.mm"
include "eqbrtrd.mm"

theorem ovnlecvr
  let wph: wff ph
  let cA: class A
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cI: class I
  let cL: class L
  let cX: class X
  let vz: setvar z
  let vx: setvar x
  assume ovnlecvr.x: |- ( ph -> X e. Fin )
  assume ovnlecvr.n0: |- ( ph -> X =/= (/) )
  assume ovnlecvr.l: |- L = ( i e. ( ( RR X. RR ) ^m X ) |-> prod_ k e. X ( vol ` ( ( [,) o. i ) ` k ) ) )
  assume ovnlecvr.i: |- ( ph -> I : NN --> ( ( RR X. RR ) ^m X ) )
  assume ovnlecvr.ss: |- ( ph -> A C_ U_ j e. NN X_ k e. X ( ( [,) o. ( I ` j ) ) ` k ) )

  disjoint A i
  disjoint I i
  disjoint I j
  disjoint I k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint L i
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint A z
  disjoint i z
  disjoint I z
  disjoint j z
  disjoint k z
  disjoint L z
  disjoint X z
  disjoint k x
  assert |- ( ph -> ( ( voln* ` X ) ` A ) <_ ( sum^ ` ( j e. NN |-> ( L ` ( I ` j ) ) ) ) )

  proof
    wph
    cA
    cX
    covoln
    cfv
    cfv
    cA
    vj
    cn
    vk
    cX
    vk
    cv
    #
    cico
    vj
    cv
    #
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
    vz
    cv
    #
    vj
    cn
    cX
    @5
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
    wrex
    #
    vz
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    vj
    cn
    @1
    cI
    cfv
    #
    cL
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    cle
    wph
    vz
    cA
    vi
    vj
    vk
    @20
    cX
    ovnlecvr.x
    ovnlecvr.n0
    wph
    cA
    vj
    cn
    vk
    cX
    @0
    cico
    @22
    ccom
    #
    cfv
    #
    cixp
    #
    ciun
    #
    cr
    cX
    cmap
    co
    #
    ovnlecvr.ss
    wph
    @28
    @30
    wss
    #
    vj
    cn
    wral
    @29
    @30
    wss
    wph
    @31
    vj
    cn
    wph
    @1
    cn
    wcel
    #
    wa
    #
    vk
    @22
    cX
    @33
    @22
    @17
    wcel
    cX
    @16
    @22
    wf
    wph
    cn
    @17
    @1
    cI
    ovnlecvr.i
    ffvelrnda
    #
    @22
    @16
    cX
    elmapi
    syl
    #
    hoissrrn
    ralrimiva
    vj
    cn
    @28
    @30
    iunss
    sylibr
    sstrd
    @20
    eqid
    ovnn0val
    wph
    @20
    cxr
    wss
    #
    @25
    @20
    wcel
    #
    @21
    @25
    cle
    wbr
    @36
    wph
    @19
    vz
    cxr
    ssrab2
    a1i
    wph
    @25
    cxr
    wcel
    #
    @8
    @25
    @13
    wceq
    #
    wa
    #
    vi
    @18
    wrex
    #
    wa
    @37
    wph
    @38
    @41
    wph
    @24
    cvv
    cn
    cn
    cvv
    wcel
    #
    wph
    nnex
    a1i
    wph
    vj
    cn
    @23
    cc0
    cpnf
    cicc
    co
    #
    @24
    @33
    cc0
    cpnf
    cico
    co
    @43
    @23
    cc0
    cpnf
    icossicc
    @33
    vi
    vk
    @22
    cL
    cX
    @33
    vk
    nfv
    wph
    cX
    cfn
    wcel
    @32
    ovnlecvr.x
    adantr
    ovnlecvr.l
    @35
    hoiprodcl2
    sseldi
    @24
    eqid
    fmptd
    sge0xrcl
    wph
    cI
    @18
    wcel
    #
    cA
    @29
    wss
    #
    @25
    vj
    cn
    cX
    @27
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
    @41
    wph
    cn
    @17
    cI
    wf
    #
    @44
    ovnlecvr.i
    @17
    cvv
    wcel
    #
    @42
    wa
    @44
    @52
    wb
    @53
    @42
    @16
    cX
    cmap
    ovex
    nnex
    pm3.2i
    @17
    cn
    cI
    cvv
    cvv
    elmapg
    ax-mp
    sylibr
    wph
    @45
    @50
    ovnlecvr.ss
    wph
    @24
    @48
    csumge0
    wph
    vj
    cn
    @23
    @47
    @33
    vi
    @22
    cX
    @0
    cico
    @2
    ccom
    #
    cfv
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    @47
    @17
    cL
    cvv
    cL
    vi
    @17
    @57
    cmpt
    wceq
    @33
    ovnlecvr.l
    a1i
    @2
    @22
    wceq
    #
    @57
    @47
    wceq
    @33
    @58
    cX
    @56
    @46
    vk
    @58
    @55
    @27
    cvol
    @58
    @0
    @54
    @26
    @2
    @22
    cico
    coeq2
    fveq1d
    fveq2d
    prodeq2ad
    adantl
    @34
    @47
    cvv
    wcel
    @33
    cX
    @46
    vk
    prodex
    a1i
    fvmptd
    mpteq2dva
    fveq2d
    jca
    @40
    @51
    vi
    cI
    @18
    @2
    cI
    wceq
    #
    @8
    @45
    @39
    @50
    @59
    @7
    @29
    cA
    @59
    vj
    cn
    @6
    @28
    @59
    vk
    cX
    @5
    @27
    @59
    vk
    nfv
    @59
    @5
    @27
    wceq
    @0
    cX
    wcel
    @59
    @0
    @4
    @26
    @59
    @3
    @22
    cico
    @1
    @2
    cI
    fveq1
    coeq2d
    fveq1d
    #
    adantr
    ixpeq2d
    iuneq2d
    sseq2d
    @59
    @13
    @49
    @25
    @59
    @12
    @48
    csumge0
    @59
    vj
    cn
    @11
    @47
    @59
    cX
    @10
    @46
    vk
    @59
    @5
    @27
    cvol
    @60
    fveq2d
    prodeq2ad
    mpteq2dv
    fveq2d
    eqeq2d
    anbi12d
    rspcev
    syl2anc
    jca
    @19
    @41
    vz
    @25
    cxr
    @9
    @25
    wceq
    #
    @15
    @40
    vi
    @18
    @61
    @14
    @39
    @8
    @9
    @25
    @13
    eqeq1
    anbi2d
    rexbidv
    elrab
    sylibr
    @20
    @25
    infxrlb
    syl2anc
    eqbrtrd
end
