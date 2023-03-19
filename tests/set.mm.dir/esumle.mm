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
include "ralrimiva.mm"
include "nfcv.mm"
include "esumcl.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "cv.mm"
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
include "esumadd.mm"
include "xrge0npcan.mm"
include "esumeq2dv.mm"
include "eqtr3d.mm"

theorem esumle
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  assume esumadd.0: |- ( ph -> A e. V )
  assume esumadd.1: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume esumadd.2: |- ( ( ph /\ k e. A ) -> C e. ( 0 [,] +oo ) )
  assume esumle.3: |- ( ( ph /\ k e. A ) -> B <_ C )

  disjoint A k
  disjoint V k
  disjoint k ph
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
    esumadd.0
    wph
    @14
    vk
    cA
    esumadd.1
    ralrimiva
    cA
    cB
    vk
    cV
    vk
    cA
    nfcv
    #
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
    esumadd.0
    wph
    @17
    vk
    cA
    wph
    vk
    cv
    cA
    wcel
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
    esumadd.2
    sseldi
    #
    @19
    cB
    @19
    @11
    cxr
    cB
    @12
    esumadd.1
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
    esumle.3
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
    ralrimiva
    cA
    @2
    vk
    cV
    @15
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
    esumadd.0
    @29
    esumadd.1
    esumadd
    wph
    cA
    @34
    cC
    vk
    @19
    cC
    @11
    wcel
    @14
    @26
    @34
    cC
    wceq
    esumadd.2
    esumadd.1
    esumle.3
    cC
    cB
    xrge0npcan
    syl3anc
    esumeq2dv
    eqtr3d
    breqtrd
end
