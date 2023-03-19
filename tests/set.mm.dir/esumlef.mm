include "cesum.mm"
include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "wbr.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "wral.mm"
include "cv.mm"
include "ex.mm"
include "ralrimi.mm"
include "esumcl.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "wa.mm"
include "xnegcld.mm"
include "xaddcld.mm"
include "wb.mm"
include "xsubge0.mm"
include "mpbird.mm"
include "pnfge.mm"
include "syl.mm"
include "w3a.mm"
include "0xr.mm"
include "pnfxr.mm"
include "elicc1.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "a1i.mm"
include "elicc4.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "simpld.mm"
include "xraddge02.mm"
include "imp.mm"
include "syl21anc.mm"
include "wceq.mm"
include "xaddcom.mm"
include "breqtrd.mm"
include "esumaddf.mm"
include "xrge0npcan.mm"
include "esumeq2d.mm"
include "eqtr3d.mm"

theorem esumlef
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  assume esumaddf.0: |- F/ k ph
  assume esumaddf.a: |- F/_ k A
  assume esumaddf.1: |- ( ph -> A e. V )
  assume esumaddf.2: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume esumaddf.3: |- ( ( ph /\ k e. A ) -> C e. ( 0 [,] +oo ) )
  assume esumlef.3: |- ( ( ph /\ k e. A ) -> B <_ C )

  disjoint V k
  assert |- ( ph -> sum* k e. A B <_ sum* k e. A C )

  proof
    wph
    cA
    cB
    vk
    cesum
    #
    cA
    cC
    cB
    cxne
    #
    cxad
    co
    #
    vk
    cesum
    #
    @0
    cxad
    co
    #
    cA
    cC
    vk
    cesum
    #
    cle
    wph
    @0
    @0
    @3
    cxad
    co
    #
    @4
    cle
    wph
    @0
    cxr
    wcel
    #
    @3
    cxr
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    @0
    @6
    cle
    wbr
    #
    wph
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @0
    cc0
    cpnf
    iccssxr
    #
    wph
    cA
    cV
    wcel
    #
    cB
    @11
    wcel
    #
    vk
    cA
    wral
    @0
    @11
    wcel
    esumaddf.1
    wph
    @14
    vk
    cA
    esumaddf.0
    wph
    vk
    cv
    cA
    wcel
    #
    @14
    esumaddf.2
    ex
    ralrimi
    cA
    cB
    vk
    cV
    esumaddf.a
    esumcl
    syl2anc
    sseldi
    #
    wph
    @11
    cxr
    @3
    @12
    wph
    @13
    @2
    @11
    wcel
    #
    vk
    cA
    wral
    @3
    @11
    wcel
    #
    esumaddf.1
    wph
    @17
    vk
    cA
    esumaddf.0
    wph
    @15
    @17
    wph
    @15
    wa
    #
    @2
    cxr
    wcel
    #
    cc0
    @2
    cle
    wbr
    #
    @2
    cpnf
    cle
    wbr
    #
    @17
    @19
    cC
    @1
    @19
    @11
    cxr
    cC
    @12
    esumaddf.3
    sseldi
    #
    @19
    cB
    @19
    @11
    cxr
    cB
    @12
    esumaddf.2
    sseldi
    #
    xnegcld
    xaddcld
    #
    @19
    @21
    cB
    cC
    cle
    wbr
    #
    esumlef.3
    @19
    cC
    cxr
    wcel
    cB
    cxr
    wcel
    @21
    @26
    wb
    @23
    @24
    cC
    cB
    xsubge0
    syl2anc
    mpbird
    @19
    @20
    @22
    @25
    @2
    pnfge
    syl
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @17
    @20
    @21
    @22
    w3a
    wb
    0xr
    pnfxr
    cc0
    cpnf
    @2
    elicc1
    mp2an
    syl3anbrc
    #
    ex
    ralrimi
    cA
    @2
    vk
    cV
    esumaddf.a
    esumcl
    syl2anc
    #
    sseldi
    #
    wph
    @9
    @3
    cpnf
    cle
    wbr
    #
    wph
    @18
    @9
    @32
    wa
    #
    @30
    wph
    @27
    @28
    @8
    @18
    @33
    wb
    @27
    wph
    0xr
    a1i
    @28
    wph
    pnfxr
    a1i
    @31
    cc0
    cpnf
    @3
    elicc4
    syl3anc
    mpbid
    simpld
    @7
    @8
    wa
    @9
    @10
    @0
    @3
    xraddge02
    imp
    syl21anc
    wph
    @7
    @8
    @6
    @4
    wceq
    @16
    @31
    @0
    @3
    xaddcom
    syl2anc
    breqtrd
    wph
    cA
    @2
    cB
    cxad
    co
    #
    vk
    cesum
    @4
    @5
    wph
    cA
    @2
    cB
    vk
    cV
    esumaddf.0
    esumaddf.a
    esumaddf.1
    @29
    esumaddf.2
    esumaddf
    wph
    cA
    @34
    cC
    vk
    esumaddf.0
    wph
    @34
    cC
    wceq
    #
    vk
    cA
    esumaddf.0
    wph
    @15
    @35
    @19
    cC
    @11
    wcel
    @14
    @26
    @35
    esumaddf.3
    esumaddf.2
    esumlef.3
    cC
    cB
    xrge0npcan
    syl3anc
    ex
    ralrimi
    esumeq2d
    eqtr3d
    breqtrd
end
