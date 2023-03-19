include "cdif.mm"
include "cesum.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "nfv.mm"
include "difssd.mm"
include "esummono.mm"
include "cun.mm"
include "cvv.mm"
include "wcel.mm"
include "unexg.mm"
include "syl2anc.mm"
include "cv.mm"
include "wo.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "elun.mm"
include "0e0iccpnf.mm"
include "syl6eqel.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "wss.mm"
include "ssun1.mm"
include "a1i.mm"
include "undif1.mm"
include "esumeq1.mm"
include "ax-mp.mm"
include "difexg.mm"
include "syl.mm"
include "sselda.mm"
include "syldan.mm"
include "esumpad.mm"
include "syl5eqr.mm"
include "breqtrd.mm"
include "jca.mm"
include "cxr.mm"
include "wb.mm"
include "iccssxr.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfcv.mm"
include "esumcl.mm"
include "sseldi.mm"
include "xrletri3.mm"
include "mpbird.mm"

theorem esumpad2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  let cW: class W
  assume esumpad.1: |- ( ph -> A e. V )
  assume esumpad.2: |- ( ph -> B e. W )
  assume esumpad.3: |- ( ( ph /\ k e. A ) -> C e. ( 0 [,] +oo ) )
  assume esumpad.4: |- ( ( ph /\ k e. B ) -> C = 0 )

  disjoint A k
  disjoint B k
  disjoint V k
  disjoint k ph
  assert |- ( ph -> sum* k e. ( A \ B ) C = sum* k e. A C )

  proof
    wph
    cA
    cB
    cdif
    #
    cC
    vk
    cesum
    #
    cA
    cC
    vk
    cesum
    #
    wceq
    #
    @1
    @2
    cle
    wbr
    #
    @2
    @1
    cle
    wbr
    #
    wa
    #
    wph
    @4
    @5
    wph
    @0
    cC
    cA
    vk
    cV
    wph
    vk
    nfv
    #
    esumpad.1
    esumpad.3
    wph
    cA
    cB
    difssd
    #
    esummono
    wph
    @2
    cA
    cB
    cun
    #
    cC
    vk
    cesum
    #
    @1
    cle
    wph
    cA
    cC
    @9
    vk
    cvv
    @7
    wph
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    @9
    cvv
    wcel
    esumpad.1
    esumpad.2
    cA
    cB
    cV
    cW
    unexg
    syl2anc
    vk
    cv
    #
    @9
    wcel
    wph
    @12
    cA
    wcel
    #
    @12
    cB
    wcel
    #
    wo
    cC
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @12
    cA
    cB
    elun
    wph
    @13
    @16
    @14
    esumpad.3
    wph
    @14
    wa
    cC
    cc0
    @15
    esumpad.4
    0e0iccpnf
    syl6eqel
    jaodan
    sylan2b
    cA
    @9
    wss
    wph
    cA
    cB
    ssun1
    a1i
    esummono
    wph
    @10
    @0
    cB
    cun
    #
    cC
    vk
    cesum
    #
    @1
    @17
    @9
    wceq
    @18
    @10
    wceq
    cA
    cB
    undif1
    @17
    @9
    cC
    vk
    esumeq1
    ax-mp
    wph
    @0
    cB
    cC
    vk
    cvv
    cW
    wph
    @11
    @0
    cvv
    wcel
    #
    esumpad.1
    cA
    cB
    cV
    difexg
    syl
    #
    esumpad.2
    wph
    @12
    @0
    wcel
    @13
    @16
    wph
    @0
    cA
    @12
    @8
    sselda
    esumpad.3
    syldan
    #
    esumpad.4
    esumpad
    syl5eqr
    breqtrd
    jca
    wph
    @1
    cxr
    wcel
    @2
    cxr
    wcel
    @3
    @6
    wb
    wph
    @15
    cxr
    @1
    cc0
    cpnf
    iccssxr
    #
    wph
    @19
    @16
    vk
    @0
    wral
    @1
    @15
    wcel
    @20
    wph
    @16
    vk
    @0
    @21
    ralrimiva
    @0
    cC
    vk
    cvv
    vk
    @0
    nfcv
    esumcl
    syl2anc
    sseldi
    wph
    @15
    cxr
    @2
    @22
    wph
    @11
    @16
    vk
    cA
    wral
    @2
    @15
    wcel
    esumpad.1
    wph
    @16
    vk
    cA
    esumpad.3
    ralrimiva
    cA
    cC
    vk
    cV
    vk
    cA
    nfcv
    esumcl
    syl2anc
    sseldi
    @1
    @2
    xrletri3
    syl2anc
    mpbird
end
