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
include "nfcv.mm"
include "esumcl.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "cif.mm"
include "crab.mm"
include "nfrab1.mm"
include "wss.mm"
include "ssrab2.mm"
include "a1i.mm"
include "wa.mm"
include "0xr.mm"
include "pnfxr.mm"
include "0lepnf.mm"
include "ubicc2.mm"
include "mp3an.mm"
include "wn.mm"
include "0e0iccpnf.mm"
include "ifclda.mm"
include "cdif.mm"
include "eldif.mm"
include "rabid.mm"
include "simplbi2.mm"
include "con3dimp.mm"
include "sylbi.mm"
include "adantl.mm"
include "iffalsed.mm"
include "esumss.mm"
include "chash.mm"
include "cfv.mm"
include "cxmu.mm"
include "eqidd.mm"
include "simprbi.mm"
include "iftrued.mm"
include "esumeq12dvaf.mm"
include "cvv.mm"
include "ssexd.mm"
include "esumcst.mm"
include "sylancl.mm"
include "clt.mm"
include "hashxrcl.mm"
include "syl.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "rabn0.mm"
include "sylibr.mm"
include "hashgt0.mm"
include "xmulpnf1.mm"
include "3eqtrd.mm"
include "eqtr3d.mm"
include "breq1.mm"
include "pnfge.mm"
include "ax-mp.mm"
include "breq2.mm"
include "mpbiri.mm"
include "adantr.mm"
include "iccgelb.mm"
include "mp3an12.mm"
include "ifbothda.mm"
include "esumlef.mm"
include "eqbrtrrd.mm"
include "xgepnf.mm"
include "biimpd.mm"
include "sylc.mm"

theorem esumpinfval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cV: class V
  assume esumpinfval.0: |- F/ k ph
  assume esumpinfval.1: |- ( ph -> A e. V )
  assume esumpinfval.2: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume esumpinfval.3: |- ( ph -> E. k e. A B = +oo )

  disjoint A k
  disjoint V k
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
    esumpinfval.1
    wph
    @5
    vk
    cA
    esumpinfval.0
    wph
    vk
    cv
    #
    cA
    wcel
    #
    @5
    esumpinfval.2
    ex
    ralrimi
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
    wph
    cA
    cB
    cpnf
    wceq
    #
    cpnf
    cc0
    cif
    #
    vk
    cesum
    #
    cpnf
    @0
    cle
    wph
    @9
    vk
    cA
    crab
    #
    @10
    vk
    cesum
    #
    @11
    cpnf
    wph
    @12
    cA
    @10
    vk
    cV
    esumpinfval.0
    @9
    vk
    cA
    nfrab1
    #
    @8
    @12
    cA
    wss
    wph
    @9
    vk
    cA
    ssrab2
    a1i
    #
    esumpinfval.1
    wph
    @7
    wa
    #
    @9
    cpnf
    cc0
    @4
    cpnf
    @4
    wcel
    #
    @16
    @9
    wa
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    cc0
    cpnf
    cle
    wbr
    @17
    0xr
    pnfxr
    0lepnf
    cc0
    cpnf
    ubicc2
    mp3an
    #
    a1i
    cc0
    @4
    wcel
    @16
    @9
    wn
    #
    wa
    #
    0e0iccpnf
    a1i
    ifclda
    #
    wph
    @6
    cA
    @12
    cdif
    wcel
    #
    wa
    @9
    cpnf
    cc0
    @24
    @21
    wph
    @24
    @7
    @6
    @12
    wcel
    #
    wn
    wa
    @21
    @6
    cA
    @12
    eldif
    @7
    @9
    @25
    @25
    @7
    @9
    @9
    vk
    cA
    rabid
    #
    simplbi2
    con3dimp
    sylbi
    adantl
    iffalsed
    esumss
    wph
    @13
    @12
    cpnf
    vk
    cesum
    #
    @12
    chash
    cfv
    #
    cpnf
    cxmu
    co
    #
    cpnf
    wph
    @12
    @12
    @10
    cpnf
    vk
    esumpinfval.0
    wph
    @12
    eqidd
    @25
    @10
    cpnf
    wceq
    wph
    @25
    @9
    cpnf
    cc0
    @25
    @7
    @9
    @26
    simprbi
    iftrued
    adantl
    esumeq12dvaf
    wph
    @12
    cvv
    wcel
    #
    @17
    @27
    @29
    wceq
    wph
    @12
    cA
    cV
    esumpinfval.1
    @15
    ssexd
    #
    @20
    @12
    cpnf
    vk
    cvv
    @14
    vk
    cpnf
    nfcv
    esumcst
    sylancl
    wph
    @28
    cxr
    wcel
    #
    cc0
    @28
    clt
    wbr
    #
    @29
    cpnf
    wceq
    wph
    @30
    @32
    @31
    @12
    cvv
    hashxrcl
    syl
    wph
    @30
    @12
    c0
    wne
    #
    @33
    @31
    wph
    @9
    vk
    cA
    wrex
    @34
    esumpinfval.3
    @9
    vk
    cA
    rabn0
    sylibr
    @12
    cvv
    hashgt0
    syl2anc
    @28
    xmulpnf1
    syl2anc
    3eqtrd
    eqtr3d
    wph
    cA
    @10
    cB
    vk
    cV
    esumpinfval.0
    @8
    esumpinfval.1
    @23
    esumpinfval.2
    @9
    cpnf
    cB
    cle
    wbr
    #
    cc0
    cB
    cle
    wbr
    #
    @10
    cB
    cle
    wbr
    @16
    cpnf
    cc0
    cpnf
    @10
    cB
    cle
    breq1
    cc0
    @10
    cB
    cle
    breq1
    @9
    @35
    @16
    @9
    @35
    cpnf
    cpnf
    cle
    wbr
    #
    @19
    @37
    pnfxr
    cpnf
    pnfge
    ax-mp
    cB
    cpnf
    cpnf
    cle
    breq2
    mpbiri
    adantl
    @22
    @5
    @36
    @16
    @5
    @21
    esumpinfval.2
    adantr
    @18
    @19
    @5
    @36
    0xr
    pnfxr
    cc0
    cpnf
    cB
    iccgelb
    mp3an12
    syl
    ifbothda
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
