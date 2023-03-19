include "ciun.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "cuni.mm"
include "cres.mm"
include "csumge0.mm"
include "wcel.mm"
include "wral.mm"
include "wceq.mm"
include "cv.mm"
include "ex.mm"
include "ralrimi.mm"
include "dfiun3g.mm"
include "syl.mm"
include "fveq2d.mm"
include "wss.mm"
include "eqid.mm"
include "rnmptss.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "1stcrestlem.mm"
include "wdisj.mm"
include "disjrnmpt2.mm"
include "meadjuni.mm"
include "ccom.mm"
include "cvv.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "wrel.mm"
include "reldom.mm"
include "brrelex.mm"
include "mpan.mm"
include "fmptdf.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "cbvrabv.mm"
include "csb.mm"
include "wa.mm"
include "simpr.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfcsb1.mm"
include "nfel.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "fvmptf.mm"
include "syl2anc.mm"
include "disjeq2dv.mm"
include "wb.mm"
include "cbvdisj.mm"
include "bicomi.mm"
include "a1i.mm"
include "bitrd.mm"
include "mpbird.mm"
include "meadjiunlem.mm"
include "cbvmpt.mm"
include "coeq2i.mm"
include "eqidd.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "meaf.mm"
include "feqmptd.mm"
include "fmptco.mm"
include "nffv.mm"
include "eqcomi.mm"
include "3eqtrd.mm"
include "eqtrd.mm"

theorem meadjiun
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let cM: class M
  let vi: setvar i
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  assume meadjiun.1: |- F/ k ph
  assume meadjiun.m: |- ( ph -> M e. Meas )
  assume meadjiun.s: |- S = dom M
  assume meadjiun.b: |- ( ( ph /\ k e. A ) -> B e. S )
  assume meadjiun.a: |- ( ph -> A ~<_ _om )
  assume meadjiun.dj: |- ( ph -> Disj_ k e. A B )

  disjoint A k
  disjoint M k
  disjoint S k
  disjoint A i
  disjoint A j
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint A x
  disjoint k x
  disjoint B i
  disjoint B j
  disjoint B x
  disjoint B y
  disjoint i y
  disjoint M i
  disjoint M y
  disjoint k y
  disjoint S i
  disjoint S y
  disjoint i ph
  disjoint k x
  assert |- ( ph -> ( M ` U_ k e. A B ) = ( sum^ ` ( k e. A |-> ( M ` B ) ) ) )

  proof
    wph
    vk
    cA
    cB
    ciun
    #
    cM
    cfv
    vk
    cA
    cB
    cmpt
    #
    crn
    #
    cuni
    #
    cM
    cfv
    cM
    @2
    cres
    csumge0
    cfv
    #
    vk
    cA
    cB
    cM
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    wph
    @0
    @3
    cM
    wph
    cB
    cS
    wcel
    #
    vk
    cA
    wral
    #
    @0
    @3
    wceq
    wph
    @8
    vk
    cA
    meadjiun.1
    wph
    vk
    cv
    #
    cA
    wcel
    #
    @8
    meadjiun.b
    ex
    ralrimi
    #
    vk
    cA
    cB
    cS
    dfiun3g
    syl
    fveq2d
    wph
    vx
    cS
    cM
    @2
    meadjiun.m
    meadjiun.s
    wph
    @9
    @2
    cS
    wss
    @12
    vk
    cA
    cB
    cS
    @1
    @1
    eqid
    #
    rnmptss
    syl
    wph
    cA
    com
    cdom
    wbr
    #
    @2
    com
    cdom
    wbr
    meadjiun.a
    vk
    cA
    cB
    1stcrestlem
    syl
    wph
    vk
    cA
    cB
    wdisj
    #
    vx
    @2
    vx
    cv
    wdisj
    meadjiun.dj
    vk
    vx
    cA
    cB
    @1
    @13
    disjrnmpt2
    syl
    meadjuni
    wph
    @4
    cM
    @1
    ccom
    #
    csumge0
    cfv
    @7
    wph
    cS
    vi
    @1
    cM
    cvv
    cA
    vj
    cv
    #
    @1
    cfv
    #
    c0
    wne
    #
    vj
    cA
    crab
    meadjiun.m
    meadjiun.s
    wph
    @14
    cA
    cvv
    wcel
    #
    meadjiun.a
    cdom
    wrel
    @14
    @20
    reldom
    cA
    com
    cdom
    brrelex
    mpan
    syl
    wph
    vk
    cA
    cB
    cS
    @1
    meadjiun.1
    meadjiun.b
    @13
    fmptdf
    @19
    vi
    cv
    #
    @1
    cfv
    #
    c0
    wne
    vj
    vi
    cA
    @17
    @21
    wceq
    @18
    @22
    c0
    @17
    @21
    @1
    fveq2
    neeq1d
    cbvrabv
    wph
    vi
    cA
    @22
    wdisj
    #
    @15
    meadjiun.dj
    wph
    @23
    vi
    cA
    vk
    @21
    cB
    csb
    #
    wdisj
    #
    @15
    wph
    vi
    cA
    @22
    @24
    wph
    @21
    cA
    wcel
    #
    wa
    #
    @26
    @24
    cS
    wcel
    #
    @22
    @24
    wceq
    wph
    @26
    simpr
    wph
    @11
    wa
    #
    @8
    wi
    @27
    @28
    wi
    vk
    vi
    @27
    @28
    vk
    wph
    @26
    vk
    meadjiun.1
    @26
    vk
    nfv
    nfan
    vk
    @24
    cS
    vk
    @21
    cB
    vk
    @21
    nfcv
    #
    nfcsb1
    #
    vk
    cS
    nfcv
    nfel
    nfim
    @10
    @21
    wceq
    #
    @29
    @27
    @8
    @28
    @32
    @11
    @26
    wph
    @10
    @21
    cA
    eleq1
    anbi2d
    @32
    cB
    @24
    cS
    vk
    @21
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    meadjiun.b
    chvar
    #
    vk
    @21
    cB
    @24
    cA
    @1
    cS
    @30
    @31
    @33
    @13
    fvmptf
    syl2anc
    disjeq2dv
    @25
    @15
    wb
    wph
    @15
    @25
    vk
    vi
    cA
    cB
    @24
    vi
    cB
    nfcv
    #
    @31
    @33
    cbvdisj
    bicomi
    a1i
    bitrd
    mpbird
    meadjiunlem
    wph
    @16
    @6
    csumge0
    wph
    @16
    cM
    vi
    cA
    @24
    cmpt
    #
    ccom
    #
    vi
    cA
    @24
    cM
    cfv
    #
    cmpt
    #
    @6
    @16
    @37
    wceq
    wph
    @1
    @36
    cM
    vk
    vi
    cA
    cB
    @24
    @35
    @31
    @33
    cbvmpt
    coeq2i
    a1i
    wph
    vi
    vy
    cA
    cS
    @24
    vy
    cv
    #
    cM
    cfv
    @38
    @36
    cM
    @34
    wph
    @36
    eqidd
    wph
    vy
    cS
    cc0
    cpnf
    cicc
    co
    cM
    wph
    cS
    cM
    meadjiun.m
    meadjiun.s
    meaf
    feqmptd
    @40
    @24
    cM
    fveq2
    fmptco
    @39
    @6
    wceq
    wph
    @6
    @39
    vk
    vi
    cA
    @5
    @38
    vi
    @5
    nfcv
    vk
    @24
    cM
    vk
    cM
    nfcv
    @31
    nffv
    @32
    cB
    @24
    cM
    @33
    fveq2d
    cbvmpt
    eqcomi
    a1i
    3eqtrd
    fveq2d
    eqtrd
    3eqtrd
end
