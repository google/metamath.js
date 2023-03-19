include "cpr.mm"
include "cesum.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "csn.mm"
include "simpr.mm"
include "dfsn2.mm"
include "preq2.mm"
include "syl5req.mm"
include "esumeq1.mm"
include "3syl.mm"
include "esumsn.mm"
include "adantr.mm"
include "eqtrd.mm"
include "cc0.mm"
include "cpnf.mm"
include "wo.mm"
include "oveq2.mm"
include "cxr.mm"
include "wcel.mm"
include "0xr.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "xaddid1.mm"
include "syl.mm"
include "cmnf.mm"
include "wne.mm"
include "pnfxr.mm"
include "pnfnemnf.mm"
include "neeq1.mm"
include "xaddpnf1.mm"
include "syl2anc.mm"
include "id.mm"
include "3eqtr4d.mm"
include "jaoi.mm"
include "syl6.mm"
include "imp.mm"
include "cv.mm"
include "simpll.mm"
include "wi.mm"
include "eqeq2.mm"
include "biimprd.mm"
include "cicc.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "3eqtr2d.mm"
include "adantlr.mm"
include "esumpr.mm"
include "pm2.61dane.mm"

theorem esumpr2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cE: class E
  let cV: class V
  let cW: class W
  assume esumpr.1: |- ( ( ph /\ k = A ) -> C = D )
  assume esumpr.2: |- ( ( ph /\ k = B ) -> C = E )
  assume esumpr.3: |- ( ph -> A e. V )
  assume esumpr.4: |- ( ph -> B e. W )
  assume esumpr.5: |- ( ph -> D e. ( 0 [,] +oo ) )
  assume esumpr.6: |- ( ph -> E e. ( 0 [,] +oo ) )
  assume esumpr2.1: |- ( ph -> ( A = B -> ( D = 0 \/ D = +oo ) ) )

  disjoint A k
  disjoint B k
  disjoint D k
  disjoint E k
  disjoint k ph
  disjoint V k
  disjoint W k
  assert |- ( ph -> sum* k e. { A , B } C = ( D +e E ) )

  proof
    wph
    cA
    cB
    cpr
    #
    cC
    vk
    cesum
    #
    cD
    cE
    cxad
    co
    #
    wceq
    cA
    cB
    wph
    cA
    cB
    wceq
    #
    wa
    #
    @1
    cD
    cD
    cD
    cxad
    co
    #
    @2
    @4
    @1
    cA
    csn
    #
    cC
    vk
    cesum
    #
    cD
    @4
    @3
    @0
    @6
    wceq
    @1
    @7
    wceq
    wph
    @3
    simpr
    #
    @3
    @6
    cA
    cA
    cpr
    @0
    cA
    dfsn2
    cA
    cB
    cA
    preq2
    syl5req
    @0
    @6
    cC
    vk
    esumeq1
    3syl
    wph
    @7
    cD
    wceq
    @3
    wph
    cC
    cD
    vk
    cA
    cV
    esumpr.1
    esumpr.3
    esumpr.5
    esumsn
    adantr
    eqtrd
    wph
    @3
    @5
    cD
    wceq
    #
    wph
    @3
    cD
    cc0
    wceq
    #
    cD
    cpnf
    wceq
    #
    wo
    @9
    esumpr2.1
    @10
    @9
    @11
    @10
    @5
    cD
    cc0
    cxad
    co
    #
    cD
    cD
    cc0
    cD
    cxad
    oveq2
    @10
    cD
    cxr
    wcel
    #
    @12
    cD
    wceq
    @10
    @13
    cc0
    cxr
    wcel
    0xr
    cD
    cc0
    cxr
    eleq1
    mpbiri
    cD
    xaddid1
    syl
    eqtrd
    @11
    cD
    cpnf
    cxad
    co
    #
    cpnf
    @5
    cD
    @11
    @13
    cD
    cmnf
    wne
    #
    @14
    cpnf
    wceq
    @11
    @13
    cpnf
    cxr
    wcel
    pnfxr
    cD
    cpnf
    cxr
    eleq1
    mpbiri
    @11
    @15
    cpnf
    cmnf
    wne
    pnfnemnf
    cD
    cpnf
    cmnf
    neeq1
    mpbiri
    cD
    xaddpnf1
    syl2anc
    cD
    cpnf
    cD
    cxad
    oveq2
    @11
    id
    3eqtr4d
    jaoi
    syl6
    imp
    @4
    cD
    cE
    cD
    cxad
    @4
    cB
    csn
    cC
    vk
    cesum
    #
    cD
    cE
    @4
    cC
    cD
    vk
    cB
    cW
    @4
    vk
    cv
    #
    cB
    wceq
    #
    wa
    wph
    @17
    cA
    wceq
    #
    cC
    cD
    wceq
    #
    wph
    @3
    @18
    simpll
    @4
    @18
    @19
    @4
    @3
    @18
    @19
    wi
    @8
    @3
    @19
    @18
    cA
    cB
    @17
    eqeq2
    biimprd
    syl
    imp
    esumpr.1
    syl2anc
    wph
    cB
    cW
    wcel
    #
    @3
    esumpr.4
    adantr
    wph
    cD
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @3
    esumpr.5
    adantr
    esumsn
    wph
    @16
    cE
    wceq
    @3
    wph
    cC
    cE
    vk
    cB
    cW
    esumpr.2
    esumpr.4
    esumpr.6
    esumsn
    adantr
    eqtr3d
    oveq2d
    3eqtr2d
    wph
    cA
    cB
    wne
    #
    wa
    cA
    cB
    cC
    cD
    vk
    cE
    cV
    cW
    wph
    @19
    @20
    @24
    esumpr.1
    adantlr
    wph
    @18
    cC
    cE
    wceq
    @24
    esumpr.2
    adantlr
    wph
    cA
    cV
    wcel
    @24
    esumpr.3
    adantr
    wph
    @21
    @24
    esumpr.4
    adantr
    wph
    @23
    @24
    esumpr.5
    adantr
    wph
    cE
    @22
    wcel
    @24
    esumpr.6
    adantr
    wph
    @24
    simpr
    esumpr
    pm2.61dane
end
