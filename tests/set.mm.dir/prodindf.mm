include "cv.mm"
include "cfv.mm"
include "cind.mm"
include "cprod.mm"
include "c1.mm"
include "wceq.mm"
include "wral.mm"
include "cc0.mm"
include "cif.mm"
include "crn.mm"
include "wss.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "wf.mm"
include "indf.mm"
include "syl2anc.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "ffvelrnd.mm"
include "fprodex01.mm"
include "wb.mm"
include "eqeq1d.mm"
include "cbvralv.mm"
include "a1i.mm"
include "ifbid.mm"
include "cmpt.mm"
include "eqid.mm"
include "rnmptss.mm"
include "nfv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfcv.mm"
include "nfss.mm"
include "nfan.mm"
include "simplr.mm"
include "feqmptd.mm"
include "eqidd.mm"
include "fveq12d.mm"
include "ralrimivw.mm"
include "r19.21bi.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "fneq1d.mm"
include "mpbid.mm"
include "simpr.mm"
include "fnfvelrn.mm"
include "eqeltrd.mm"
include "adantlr.mm"
include "sseldd.mm"
include "ex.mm"
include "ralrimi.mm"
include "impbid2.mm"
include "ind1a.mm"
include "syl3anc.mm"
include "ralbidva.mm"
include "rneqd.mm"
include "sseq1d.mm"
include "3bitr4d.mm"
include "3eqtrd.mm"

theorem prodindf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cO: class O
  let cV: class V
  let vl: setvar l
  assume prodindf.1: |- ( ph -> O e. V )
  assume prodindf.2: |- ( ph -> A e. Fin )
  assume prodindf.3: |- ( ph -> B C_ O )
  assume prodindf.4: |- ( ph -> F : A --> O )

  disjoint A k
  disjoint B k
  disjoint F k
  disjoint O k
  disjoint k ph
  disjoint A l
  disjoint k l
  disjoint B l
  disjoint F l
  disjoint O l
  disjoint l ph
  assert |- ( ph -> prod_ k e. A ( ( ( _Ind ` O ) ` B ) ` ( F ` k ) ) = if ( ran F C_ B , 1 , 0 ) )

  proof
    wph
    cA
    vk
    cv
    #
    cF
    cfv
    #
    cB
    cO
    cind
    cfv
    cfv
    #
    cfv
    #
    vk
    cprod
    vl
    cv
    #
    cF
    cfv
    #
    @2
    cfv
    #
    c1
    wceq
    #
    vl
    cA
    wral
    #
    c1
    cc0
    cif
    @3
    c1
    wceq
    #
    vk
    cA
    wral
    #
    c1
    cc0
    cif
    cF
    crn
    #
    cB
    wss
    #
    c1
    cc0
    cif
    wph
    cA
    @3
    @6
    vk
    vl
    @0
    @4
    wceq
    @1
    @5
    @2
    @0
    @4
    cF
    fveq2
    fveq2d
    prodindf.2
    wph
    @0
    cA
    wcel
    #
    wa
    #
    cO
    cc0
    c1
    cpr
    #
    @1
    @2
    wph
    cO
    @15
    @2
    wf
    #
    @13
    wph
    cO
    cV
    wcel
    #
    cB
    cO
    wss
    #
    @16
    prodindf.1
    prodindf.3
    cB
    cO
    cV
    indf
    syl2anc
    adantr
    wph
    cA
    cO
    @0
    cF
    prodindf.4
    ffvelrnda
    #
    ffvelrnd
    fprodex01
    wph
    @8
    @10
    c1
    cc0
    @8
    @10
    wb
    wph
    @7
    @9
    vl
    vk
    cA
    @4
    @0
    wceq
    #
    @6
    @3
    c1
    @20
    @5
    @1
    @2
    @4
    @0
    cF
    fveq2
    fveq2d
    eqeq1d
    cbvralv
    a1i
    ifbid
    wph
    @10
    @12
    c1
    cc0
    wph
    @1
    cB
    wcel
    #
    vk
    cA
    wral
    #
    vk
    cA
    @1
    cmpt
    #
    crn
    #
    cB
    wss
    #
    @10
    @12
    wph
    @22
    @25
    vk
    cA
    @1
    cB
    @23
    @23
    eqid
    rnmptss
    wph
    @25
    @22
    wph
    @25
    wa
    #
    @21
    vk
    cA
    wph
    @25
    vk
    wph
    vk
    nfv
    vk
    @24
    cB
    vk
    @23
    vk
    cA
    @1
    nfmpt1
    nfrn
    vk
    cB
    nfcv
    nfss
    nfan
    @26
    @13
    @21
    @26
    @13
    wa
    @24
    cB
    @1
    wph
    @25
    @13
    simplr
    wph
    @13
    @1
    @24
    wcel
    @25
    @14
    @1
    @0
    @23
    cfv
    #
    @24
    wph
    @1
    @27
    wceq
    #
    vk
    cA
    wph
    @28
    vk
    cA
    wph
    @0
    @0
    cF
    @23
    wph
    vk
    cA
    cO
    cF
    prodindf.4
    feqmptd
    #
    wph
    @0
    eqidd
    fveq12d
    ralrimivw
    r19.21bi
    @14
    @23
    cA
    wfn
    #
    @13
    @27
    @24
    wcel
    wph
    @30
    @13
    wph
    cF
    cA
    wfn
    #
    @30
    wph
    cA
    cO
    cF
    wf
    @31
    prodindf.4
    cA
    cO
    cF
    ffn
    syl
    wph
    cA
    cF
    @23
    @29
    fneq1d
    mpbid
    adantr
    wph
    @13
    simpr
    cA
    @0
    @23
    fnfvelrn
    syl2anc
    eqeltrd
    adantlr
    sseldd
    ex
    ralrimi
    ex
    impbid2
    wph
    @9
    @21
    vk
    cA
    @14
    @17
    @18
    @1
    cO
    wcel
    @9
    @21
    wb
    wph
    @17
    @13
    prodindf.1
    adantr
    wph
    @18
    @13
    prodindf.3
    adantr
    @19
    cB
    cO
    cV
    @1
    ind1a
    syl3anc
    ralbidva
    wph
    @11
    @24
    cB
    wph
    cF
    @23
    @29
    rneqd
    sseq1d
    3bitr4d
    ifbid
    3eqtrd
end
