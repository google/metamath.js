include "cesum.mm"
include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "iccssxr.mm"
include "wral.mm"
include "cv.mm"
include "ex.mm"
include "ralrimi.mm"
include "esumcl.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "chash.mm"
include "cfv.mm"
include "cxmu.mm"
include "clt.mm"
include "wi.mm"
include "0xr.mm"
include "xrltle.mm"
include "sylancr.mm"
include "mpd.mm"
include "pnfge.mm"
include "syl.mm"
include "w3a.mm"
include "wb.mm"
include "pnfxr.mm"
include "elicc1.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "nfcv.mm"
include "esumcst.mm"
include "cfn.mm"
include "wn.mm"
include "hashinf.mm"
include "oveq1d.mm"
include "xmulpnf2.mm"
include "3eqtrd.mm"
include "adantr.mm"
include "esumlef.mm"
include "eqbrtrrd.mm"
include "xgepnf.mm"
include "biimpd.mm"
include "sylc.mm"

theorem esumpinfsum
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cV: class V
  assume esumpinfsum.p: |- F/ k ph
  assume esumpinfsum.a: |- F/_ k A
  assume esumpinfsum.1: |- ( ph -> A e. V )
  assume esumpinfsum.2: |- ( ph -> -. A e. Fin )
  assume esumpinfsum.3: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume esumpinfsum.4: |- ( ( ph /\ k e. A ) -> M <_ B )
  assume esumpinfsum.5: |- ( ph -> M e. RR* )
  assume esumpinfsum.6: |- ( ph -> 0 < M )

  disjoint V k
  disjoint M k
  assert |- ( ph -> sum* k e. A B = +oo )

  proof
    wph
    cA
    cB
    vk
    cesum
    #
    cxr
    wcel
    #
    cpnf
    @0
    cle
    wbr
    #
    @0
    cpnf
    wceq
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
    wph
    cA
    cV
    wcel
    #
    cB
    @4
    wcel
    #
    vk
    cA
    wral
    @0
    @4
    wcel
    esumpinfsum.1
    wph
    @6
    vk
    cA
    esumpinfsum.p
    wph
    vk
    cv
    cA
    wcel
    #
    @6
    esumpinfsum.3
    ex
    ralrimi
    cA
    cB
    vk
    cV
    esumpinfsum.a
    esumcl
    syl2anc
    sseldi
    wph
    cA
    cM
    vk
    cesum
    #
    cpnf
    @0
    cle
    wph
    @8
    cA
    chash
    cfv
    #
    cM
    cxmu
    co
    #
    cpnf
    cM
    cxmu
    co
    #
    cpnf
    wph
    @5
    cM
    @4
    wcel
    #
    @8
    @10
    wceq
    esumpinfsum.1
    wph
    cM
    cxr
    wcel
    #
    cc0
    cM
    cle
    wbr
    #
    cM
    cpnf
    cle
    wbr
    #
    @12
    esumpinfsum.5
    wph
    cc0
    cM
    clt
    wbr
    #
    @14
    esumpinfsum.6
    wph
    cc0
    cxr
    wcel
    #
    @13
    @16
    @14
    wi
    0xr
    esumpinfsum.5
    cc0
    cM
    xrltle
    sylancr
    mpd
    wph
    @13
    @15
    esumpinfsum.5
    cM
    pnfge
    syl
    @17
    cpnf
    cxr
    wcel
    @12
    @13
    @14
    @15
    w3a
    wb
    0xr
    pnfxr
    cc0
    cpnf
    cM
    elicc1
    mp2an
    syl3anbrc
    #
    cA
    cM
    vk
    cV
    esumpinfsum.a
    vk
    cM
    nfcv
    esumcst
    syl2anc
    wph
    @9
    cpnf
    cM
    cxmu
    wph
    @5
    cA
    cfn
    wcel
    wn
    @9
    cpnf
    wceq
    esumpinfsum.1
    esumpinfsum.2
    cA
    cV
    hashinf
    syl2anc
    oveq1d
    wph
    @13
    @16
    @11
    cpnf
    wceq
    esumpinfsum.5
    esumpinfsum.6
    cM
    xmulpnf2
    syl2anc
    3eqtrd
    wph
    cA
    cM
    cB
    vk
    cV
    esumpinfsum.p
    esumpinfsum.a
    esumpinfsum.1
    wph
    @12
    @7
    @18
    adantr
    esumpinfsum.3
    esumpinfsum.4
    esumlef
    eqbrtrrd
    @1
    @2
    @3
    @0
    xgepnf
    biimpd
    sylc
end
