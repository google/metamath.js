include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "cfv.mm"
include "cc0.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "c1.mm"
include "cn0.mm"
include "cc.mm"
include "wf.mm"
include "cv.mm"
include "cbcc.mm"
include "co.mm"
include "adantr.mm"
include "simpr.mm"
include "bcccl.mm"
include "fmptd.mm"
include "cabs.mm"
include "cico.mm"
include "ccnv.mm"
include "cima.mm"
include "eleq2i.mm"
include "cr.mm"
include "wfn.mm"
include "wb.mm"
include "absf.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "bitri.mm"
include "simplbi.mm"
include "adantl.mm"
include "clt.mm"
include "wbr.mm"
include "simprbi.mm"
include "cle.mm"
include "cxr.mm"
include "w3a.mm"
include "0re.mm"
include "crab.mm"
include "csup.mm"
include "wss.mm"
include "ssrab2.mm"
include "ressxr.mm"
include "sstri.mm"
include "supxrcl.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "elico2.mm"
include "mp2an.mm"
include "simp3bi.mm"
include "syl.mm"
include "radcnvlt2.mm"
include "cn.mm"
include "cmul.mm"
include "cmin.mm"
include "cexp.mm"
include "cmpt.mm"
include "wceq.mm"
include "cvv.mm"
include "a1i.mm"
include "simplr.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "mpteq2dva.mm"
include "nnex.mm"
include "mptex.mm"
include "fvmptd.mm"
include "sylan2.mm"
include "seqeq3d.mm"
include "eqid.mm"
include "dvradcnv2.mm"
include "eqeltrd.mm"
include "jca.mm"

theorem binomcxplemcvg
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cJ: class J
  let vr: setvar r
  let vb: setvar b
  assume binomcxp.a: |- ( ph -> A e. RR+ )
  assume binomcxp.b: |- ( ph -> B e. RR )
  assume binomcxp.lt: |- ( ph -> ( abs ` B ) < ( abs ` A ) )
  assume binomcxp.c: |- ( ph -> C e. CC )
  assume binomcxplem.f: |- F = ( j e. NN0 |-> ( C _Cc j ) )
  assume binomcxplem.s: |- S = ( b e. CC |-> ( k e. NN0 |-> ( ( F ` k ) x. ( b ^ k ) ) ) )
  assume binomcxplem.r: |- R = sup ( { r e. RR | seq 0 ( + , ( S ` r ) ) e. dom ~~> } , RR* , < )
  assume binomcxplem.e: |- E = ( b e. CC |-> ( k e. NN |-> ( ( k x. ( F ` k ) ) x. ( b ^ ( k - 1 ) ) ) ) )
  assume binomcxplem.d: |- D = ( `' abs " ( 0 [,) R ) )

  disjoint b k
  disjoint b ph
  disjoint k ph
  disjoint F b
  disjoint F k
  disjoint J b
  disjoint J k
  disjoint b r
  disjoint J r
  disjoint j ph
  disjoint S r
  assert |- ( ( ph /\ J e. D ) -> ( seq 0 ( + , ( S ` J ) ) e. dom ~~> /\ seq 1 ( + , ( E ` J ) ) e. dom ~~> ) )

  proof
    wph
    cJ
    cD
    wcel
    #
    wa
    #
    caddc
    cJ
    cS
    cfv
    cc0
    cseq
    cli
    cdm
    #
    wcel
    caddc
    cJ
    cE
    cfv
    #
    c1
    cseq
    #
    @2
    wcel
    @1
    vb
    cF
    cR
    vk
    cS
    cJ
    vr
    binomcxplem.s
    wph
    cn0
    cc
    cF
    wf
    @0
    wph
    vj
    cn0
    cC
    vj
    cv
    #
    cbcc
    co
    cc
    cF
    wph
    @5
    cn0
    wcel
    #
    wa
    cC
    @5
    wph
    cC
    cc
    wcel
    @6
    binomcxp.c
    adantr
    wph
    @6
    simpr
    bcccl
    binomcxplem.f
    fmptd
    adantr
    #
    binomcxplem.r
    @0
    cJ
    cc
    wcel
    #
    wph
    @0
    @8
    cJ
    cabs
    cfv
    #
    cc0
    cR
    cico
    co
    #
    wcel
    #
    @0
    cJ
    cabs
    ccnv
    @10
    cima
    #
    wcel
    #
    @8
    @11
    wa
    #
    cD
    @12
    cJ
    binomcxplem.d
    eleq2i
    cc
    cr
    cabs
    wf
    cabs
    cc
    wfn
    @13
    @14
    wb
    absf
    cc
    cr
    cabs
    ffn
    cc
    cJ
    @10
    cabs
    elpreima
    mp2b
    bitri
    #
    simplbi
    #
    adantl
    #
    @0
    @9
    cR
    clt
    wbr
    #
    wph
    @0
    @11
    @18
    @0
    @8
    @11
    @15
    simprbi
    @11
    @9
    cr
    wcel
    #
    cc0
    @9
    cle
    wbr
    #
    @18
    cc0
    cr
    wcel
    cR
    cxr
    wcel
    @11
    @19
    @20
    @18
    w3a
    wb
    0re
    cR
    caddc
    vr
    cv
    cS
    cfv
    cc0
    cseq
    @2
    wcel
    #
    vr
    cr
    crab
    #
    cxr
    clt
    csup
    #
    cxr
    binomcxplem.r
    @22
    cxr
    wss
    @23
    cxr
    wcel
    @22
    cr
    cxr
    @21
    vr
    cr
    ssrab2
    ressxr
    sstri
    @22
    supxrcl
    ax-mp
    eqeltri
    cc0
    cR
    @9
    elico2
    mp2an
    simp3bi
    syl
    adantl
    #
    radcnvlt2
    @1
    @4
    caddc
    vk
    cn
    vk
    cv
    #
    @25
    cF
    cfv
    cmul
    co
    #
    cJ
    @25
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    c1
    cseq
    @2
    @1
    @3
    @30
    caddc
    c1
    @0
    wph
    @8
    @3
    @30
    wceq
    @16
    wph
    @8
    wa
    #
    vb
    cJ
    vk
    cn
    @26
    vb
    cv
    #
    @27
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    @30
    cc
    cE
    cvv
    cE
    vb
    cc
    @35
    cmpt
    wceq
    @31
    binomcxplem.e
    a1i
    @31
    @32
    cJ
    wceq
    #
    wa
    #
    vk
    cn
    @34
    @29
    @37
    @25
    cn
    wcel
    #
    wa
    #
    @33
    @28
    @26
    cmul
    @39
    @32
    cJ
    @27
    cexp
    @31
    @36
    @38
    simplr
    oveq1d
    oveq2d
    mpteq2dva
    wph
    @8
    simpr
    @30
    cvv
    wcel
    @31
    vk
    cn
    @29
    nnex
    mptex
    a1i
    fvmptd
    sylan2
    seqeq3d
    @1
    vb
    cF
    cR
    vk
    cS
    @30
    cJ
    vr
    binomcxplem.s
    binomcxplem.r
    @30
    eqid
    @7
    @17
    @24
    dvradcnv2
    eqeltrd
    jca
end
