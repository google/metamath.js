include "cesum.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "cc0.mm"
include "wbr.mm"
include "cpnf.mm"
include "cicc.mm"
include "wcel.mm"
include "cvv.mm"
include "wral.mm"
include "difexg.mm"
include "syl.mm"
include "cv.mm"
include "wa.mm"
include "simpr.mm"
include "eldifad.mm"
include "syldan.mm"
include "ex.mm"
include "ralrimi.mm"
include "nfcv.mm"
include "esumcl.mm"
include "syl2anc.mm"
include "cxr.mm"
include "elxrge0.mm"
include "simprbi.mm"
include "wi.mm"
include "iccssxr.mm"
include "ssexd.mm"
include "sselda.mm"
include "sseldi.mm"
include "xraddge02.mm"
include "mpd.mm"
include "cun.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "disjdif.mm"
include "a1i.mm"
include "esumsplit.mm"
include "wss.mm"
include "undif.mm"
include "sylib.mm"
include "esumeq1d.mm"
include "eqtr3d.mm"
include "breqtrd.mm"

theorem esummono
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  assume esummono.f: |- F/ k ph
  assume esummono.c: |- ( ph -> C e. V )
  assume esummono.b: |- ( ( ph /\ k e. C ) -> B e. ( 0 [,] +oo ) )
  assume esummono.a: |- ( ph -> A C_ C )

  disjoint A k
  disjoint C k
  assert |- ( ph -> sum* k e. A B <_ sum* k e. C B )

  proof
    wph
    cA
    cB
    vk
    cesum
    #
    @0
    cC
    cA
    cdif
    #
    cB
    vk
    cesum
    #
    cxad
    co
    #
    cC
    cB
    vk
    cesum
    #
    cle
    wph
    cc0
    @2
    cle
    wbr
    #
    @0
    @3
    cle
    wbr
    #
    wph
    @2
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @5
    wph
    @1
    cvv
    wcel
    #
    cB
    @7
    wcel
    #
    vk
    @1
    wral
    @8
    wph
    cC
    cV
    wcel
    @9
    esummono.c
    cC
    cA
    cV
    difexg
    syl
    #
    wph
    @10
    vk
    @1
    esummono.f
    wph
    vk
    cv
    #
    @1
    wcel
    #
    @10
    wph
    @13
    @12
    cC
    wcel
    #
    @10
    wph
    @13
    wa
    @12
    cC
    cA
    wph
    @13
    simpr
    eldifad
    esummono.b
    syldan
    #
    ex
    ralrimi
    @1
    cB
    vk
    cvv
    vk
    @1
    nfcv
    #
    esumcl
    syl2anc
    #
    @8
    @2
    cxr
    wcel
    #
    @5
    @2
    elxrge0
    simprbi
    syl
    wph
    @0
    cxr
    wcel
    @18
    @5
    @6
    wi
    wph
    @7
    cxr
    @0
    cc0
    cpnf
    iccssxr
    #
    wph
    cA
    cvv
    wcel
    @10
    vk
    cA
    wral
    @0
    @7
    wcel
    wph
    cA
    cC
    cV
    esummono.c
    esummono.a
    ssexd
    #
    wph
    @10
    vk
    cA
    esummono.f
    wph
    @12
    cA
    wcel
    #
    @10
    wph
    @21
    @14
    @10
    wph
    cA
    cC
    @12
    esummono.a
    sselda
    esummono.b
    syldan
    #
    ex
    ralrimi
    cA
    cB
    vk
    cvv
    vk
    cA
    nfcv
    #
    esumcl
    syl2anc
    sseldi
    wph
    @7
    cxr
    @2
    @19
    @17
    sseldi
    @0
    @2
    xraddge02
    syl2anc
    mpd
    wph
    cA
    @1
    cun
    #
    cB
    vk
    cesum
    @3
    @4
    wph
    cA
    @1
    cB
    vk
    esummono.f
    @23
    @16
    @20
    @11
    cA
    @1
    cin
    c0
    wceq
    wph
    cA
    cC
    disjdif
    a1i
    @22
    @15
    esumsplit
    wph
    @24
    cC
    cB
    vk
    esummono.f
    wph
    cA
    cC
    wss
    @24
    cC
    wceq
    esummono.a
    cA
    cC
    undif
    sylib
    esumeq1d
    eqtr3d
    breqtrd
end
