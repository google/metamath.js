include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cesum.mm"
include "cc0.mm"
include "cxad.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "cvv.mm"
include "wral.mm"
include "ovexd.mm"
include "cv.mm"
include "cn.mm"
include "elfznn.mm"
include "wa.mm"
include "cico.mm"
include "icossicc.mm"
include "sseldi.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "nfcv.mm"
include "esumcl.mm"
include "syl2anc.mm"
include "xrleid.mm"
include "syl.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "adantr.mm"
include "peano2nn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "fzss1.mm"
include "3syl.mm"
include "simpr.mm"
include "sseldd.mm"
include "syldan.mm"
include "elxrge0.mm"
include "simprbi.mm"
include "wi.mm"
include "0xr.mm"
include "a1i.mm"
include "xle2add.mm"
include "syl22anc.mm"
include "mp2and.mm"
include "wceq.mm"
include "xaddid1.mm"
include "eqcomd.mm"
include "cun.mm"
include "eluzfz.mm"
include "fzsplit.mm"
include "esumeq1.mm"
include "nfv.mm"
include "clt.mm"
include "cin.mm"
include "c0.mm"
include "nnre.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "esumsplit.mm"
include "eqtrd.mm"
include "3brtr4d.mm"

theorem esumpmono
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cM: class M
  let cN: class N
  assume esumpmono.1: |- ( ph -> M e. NN )
  assume esumpmono.2: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume esumpmono.3: |- ( ( ph /\ k e. NN ) -> A e. ( 0 [,) +oo ) )

  disjoint M k
  disjoint N k
  disjoint k ph
  assert |- ( ph -> sum* k e. ( 1 ... M ) A <_ sum* k e. ( 1 ... N ) A )

  proof
    wph
    c1
    cM
    cfz
    co
    #
    cA
    vk
    cesum
    #
    cc0
    cxad
    co
    #
    @1
    cM
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    cA
    vk
    cesum
    #
    cxad
    co
    #
    @1
    c1
    cN
    cfz
    co
    #
    cA
    vk
    cesum
    #
    cle
    wph
    @1
    @1
    cle
    wbr
    #
    cc0
    @5
    cle
    wbr
    #
    @2
    @6
    cle
    wbr
    #
    wph
    @1
    cxr
    wcel
    #
    @9
    wph
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @1
    cc0
    cpnf
    iccssxr
    #
    wph
    @0
    cvv
    wcel
    cA
    @13
    wcel
    #
    vk
    @0
    wral
    @1
    @13
    wcel
    wph
    c1
    cM
    cfz
    ovexd
    #
    wph
    @15
    vk
    @0
    vk
    cv
    #
    @0
    wcel
    wph
    @17
    cn
    wcel
    #
    @15
    @17
    cM
    elfznn
    wph
    @18
    wa
    cc0
    cpnf
    cico
    co
    @13
    cA
    cc0
    cpnf
    icossicc
    esumpmono.3
    sseldi
    #
    sylan2
    #
    ralrimiva
    @0
    cA
    vk
    cvv
    vk
    @0
    nfcv
    #
    esumcl
    syl2anc
    sseldi
    #
    @1
    xrleid
    syl
    wph
    @5
    @13
    wcel
    #
    @10
    wph
    @4
    cvv
    wcel
    @15
    vk
    @4
    wral
    @23
    wph
    @3
    cN
    cfz
    ovexd
    #
    wph
    @15
    vk
    @4
    wph
    @17
    @4
    wcel
    #
    @18
    @15
    wph
    @25
    wa
    #
    @17
    @7
    wcel
    @18
    @26
    @4
    @7
    @17
    @26
    cM
    cn
    wcel
    #
    @3
    c1
    cuz
    cfv
    #
    wcel
    @4
    @7
    wss
    wph
    @27
    @25
    esumpmono.1
    adantr
    @27
    @3
    cn
    @28
    cM
    peano2nn
    nnuz
    syl6eleq
    @3
    c1
    cN
    fzss1
    3syl
    wph
    @25
    simpr
    sseldd
    @17
    cN
    elfznn
    syl
    @19
    syldan
    #
    ralrimiva
    @4
    cA
    vk
    cvv
    vk
    @4
    nfcv
    #
    esumcl
    syl2anc
    #
    @23
    @5
    cxr
    wcel
    #
    @10
    @5
    elxrge0
    simprbi
    syl
    wph
    @12
    cc0
    cxr
    wcel
    #
    @12
    @32
    @9
    @10
    wa
    @11
    wi
    @22
    @33
    wph
    0xr
    a1i
    @22
    wph
    @13
    cxr
    @5
    @14
    @31
    sseldi
    @1
    cc0
    @1
    @5
    xle2add
    syl22anc
    mp2and
    wph
    @2
    @1
    wph
    @12
    @2
    @1
    wceq
    @22
    @1
    xaddid1
    syl
    eqcomd
    wph
    @8
    @0
    @4
    cun
    #
    cA
    vk
    cesum
    #
    @6
    wph
    cM
    @7
    wcel
    #
    @7
    @34
    wceq
    @8
    @35
    wceq
    wph
    cM
    @28
    wcel
    cN
    cM
    cuz
    cfv
    wcel
    @36
    wph
    cM
    cn
    @28
    esumpmono.1
    nnuz
    syl6eleq
    esumpmono.2
    cM
    c1
    cN
    eluzfz
    syl2anc
    cM
    c1
    cN
    fzsplit
    @7
    @34
    cA
    vk
    esumeq1
    3syl
    wph
    @0
    @4
    cA
    vk
    wph
    vk
    nfv
    @21
    @30
    @16
    @24
    wph
    @27
    cM
    @3
    clt
    wbr
    @0
    @4
    cin
    c0
    wceq
    esumpmono.1
    @27
    cM
    cM
    nnre
    ltp1d
    c1
    cM
    @3
    cN
    fzdisj
    3syl
    @20
    @29
    esumsplit
    eqtrd
    3brtr4d
end
