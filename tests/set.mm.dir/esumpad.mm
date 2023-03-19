include "cdif.mm"
include "cun.mm"
include "cesum.mm"
include "cxad.mm"
include "co.mm"
include "nfv.mm"
include "nfcv.mm"
include "wcel.mm"
include "cvv.mm"
include "elex.mm"
include "syl.mm"
include "difexg.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "disjdif.mm"
include "a1i.mm"
include "cv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "difssd.mm"
include "sselda.mm"
include "wa.mm"
include "0e0iccpnf.mm"
include "syl6eqel.mm"
include "syldan.mm"
include "esumsplit.mm"
include "undif2.mm"
include "esumeq1.mm"
include "ax-mp.mm"
include "ralrimiva.mm"
include "esumeq2d.mm"
include "esum0.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "cxr.mm"
include "iccssxr.mm"
include "wral.mm"
include "esumcl.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "xaddid1.mm"
include "3eqtr3d.mm"

theorem esumpad
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
  assert |- ( ph -> sum* k e. ( A u. B ) C = sum* k e. A C )

  proof
    wph
    cA
    cB
    cA
    cdif
    #
    cun
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
    @0
    cC
    vk
    cesum
    #
    cxad
    co
    #
    cA
    cB
    cun
    #
    cC
    vk
    cesum
    #
    @3
    wph
    cA
    @0
    cC
    vk
    wph
    vk
    nfv
    #
    vk
    cA
    nfcv
    #
    vk
    @0
    nfcv
    #
    wph
    cA
    cV
    wcel
    #
    cA
    cvv
    wcel
    esumpad.1
    cA
    cV
    elex
    syl
    wph
    cB
    cW
    wcel
    @0
    cvv
    wcel
    #
    esumpad.2
    cB
    cA
    cW
    difexg
    syl
    #
    cA
    @0
    cin
    c0
    wceq
    wph
    cA
    cB
    disjdif
    a1i
    esumpad.3
    wph
    vk
    cv
    #
    @0
    wcel
    #
    @14
    cB
    wcel
    #
    cC
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    wph
    @0
    cB
    @14
    wph
    cB
    cA
    difssd
    sselda
    #
    wph
    @16
    wa
    cC
    cc0
    @17
    esumpad.4
    0e0iccpnf
    syl6eqel
    syldan
    esumsplit
    @2
    @7
    wceq
    #
    wph
    @1
    @6
    wceq
    @20
    cA
    cB
    undif2
    @1
    @6
    cC
    vk
    esumeq1
    ax-mp
    a1i
    wph
    @5
    @3
    cc0
    cxad
    co
    #
    @3
    wph
    @4
    cc0
    @3
    cxad
    wph
    @4
    @0
    cc0
    vk
    cesum
    #
    cc0
    wph
    @0
    cC
    cc0
    vk
    @8
    wph
    cC
    cc0
    wceq
    #
    vk
    @0
    wph
    @15
    @16
    @23
    @19
    esumpad.4
    syldan
    ralrimiva
    esumeq2d
    wph
    @12
    @22
    cc0
    wceq
    @13
    @0
    vk
    cvv
    @10
    esum0
    syl
    eqtrd
    oveq2d
    wph
    @3
    cxr
    wcel
    @21
    @3
    wceq
    wph
    @17
    cxr
    @3
    cc0
    cpnf
    iccssxr
    wph
    @11
    @18
    vk
    cA
    wral
    @3
    @17
    wcel
    esumpad.1
    wph
    @18
    vk
    cA
    esumpad.3
    ralrimiva
    cA
    cC
    vk
    cV
    @9
    esumcl
    syl2anc
    sseldi
    @3
    xaddid1
    syl
    eqtrd
    3eqtr3d
end
