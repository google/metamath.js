include "csu.mm"
include "caddc.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cif.mm"
include "wss.mm"
include "cc.mm"
include "wral.mm"
include "cuz.mm"
include "cfv.mm"
include "cfn.mm"
include "wo.mm"
include "wceq.mm"
include "cun.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "sselda.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "olcd.mm"
include "sumss2.mm"
include "syl21anc.mm"
include "ssun2.mm"
include "oveq12d.mm"
include "wa.mm"
include "0cn.mm"
include "ifcl.mm"
include "sylancl.mm"
include "fsumadd.mm"
include "eleq2d.mm"
include "elun.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "iftrue.mm"
include "adantl.mm"
include "wn.mm"
include "wi.mm"
include "c0.mm"
include "noel.mm"
include "cin.mm"
include "elin.mm"
include "syl5rbbr.mm"
include "mtbii.mm"
include "imnan.mm"
include "sylibr.mm"
include "imp.mm"
include "iffalsed.mm"
include "addid1d.mm"
include "eqtrd.mm"
include "con2d.mm"
include "addid2d.mm"
include "jaodan.mm"
include "sumeq2dv.mm"
include "3eqtr2rd.mm"

theorem fsumsplit
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let vk: setvar k
  assume fsumsplit.1: |- ( ph -> ( A i^i B ) = (/) )
  assume fsumsplit.2: |- ( ph -> U = ( A u. B ) )
  assume fsumsplit.3: |- ( ph -> U e. Fin )
  assume fsumsplit.4: |- ( ( ph /\ k e. U ) -> C e. CC )

  disjoint A k
  disjoint B k
  disjoint k ph
  disjoint U k
  assert |- ( ph -> sum_ k e. U C = ( sum_ k e. A C + sum_ k e. B C ) )

  proof
    wph
    cA
    cC
    vk
    csu
    #
    cB
    cC
    vk
    csu
    #
    caddc
    co
    cU
    vk
    cv
    #
    cA
    wcel
    #
    cC
    cc0
    cif
    #
    vk
    csu
    #
    cU
    @2
    cB
    wcel
    #
    cC
    cc0
    cif
    #
    vk
    csu
    #
    caddc
    co
    cU
    @4
    @7
    caddc
    co
    #
    vk
    csu
    cU
    cC
    vk
    csu
    wph
    @0
    @5
    @1
    @8
    caddc
    wph
    cA
    cU
    wss
    cC
    cc
    wcel
    #
    vk
    cA
    wral
    cU
    cc0
    cuz
    cfv
    wss
    #
    cU
    cfn
    wcel
    #
    wo
    #
    @0
    @5
    wceq
    wph
    cA
    cB
    cun
    #
    cA
    cU
    cA
    cB
    ssun1
    fsumsplit.2
    syl5sseqr
    #
    wph
    @10
    vk
    cA
    wph
    @3
    @2
    cU
    wcel
    #
    @10
    wph
    cA
    cU
    @2
    @15
    sselda
    fsumsplit.4
    syldan
    #
    ralrimiva
    wph
    @12
    @11
    fsumsplit.3
    olcd
    #
    cA
    cU
    cC
    vk
    cc0
    sumss2
    syl21anc
    wph
    cB
    cU
    wss
    @10
    vk
    cB
    wral
    @13
    @1
    @8
    wceq
    wph
    @14
    cB
    cU
    cB
    cA
    ssun2
    fsumsplit.2
    syl5sseqr
    #
    wph
    @10
    vk
    cB
    wph
    @6
    @16
    @10
    wph
    cB
    cU
    @2
    @19
    sselda
    fsumsplit.4
    syldan
    #
    ralrimiva
    @18
    cB
    cU
    cC
    vk
    cc0
    sumss2
    syl21anc
    oveq12d
    wph
    cU
    @4
    @7
    vk
    fsumsplit.3
    wph
    @16
    wa
    #
    @10
    cc0
    cc
    wcel
    #
    @4
    cc
    wcel
    fsumsplit.4
    0cn
    @3
    cC
    cc0
    cc
    ifcl
    sylancl
    @21
    @10
    @22
    @7
    cc
    wcel
    fsumsplit.4
    0cn
    @6
    cC
    cc0
    cc
    ifcl
    sylancl
    fsumadd
    wph
    cU
    @9
    cC
    vk
    wph
    @16
    @3
    @6
    wo
    #
    @9
    cC
    wceq
    #
    wph
    @16
    @23
    wph
    @16
    @2
    @14
    wcel
    @23
    wph
    cU
    @14
    @2
    fsumsplit.2
    eleq2d
    @2
    cA
    cB
    elun
    syl6bb
    biimpa
    wph
    @3
    @24
    @6
    wph
    @3
    wa
    #
    @9
    cC
    cc0
    caddc
    co
    cC
    @25
    @4
    cC
    @7
    cc0
    caddc
    @3
    @4
    cC
    wceq
    wph
    @3
    cC
    cc0
    iftrue
    adantl
    @25
    @6
    cC
    cc0
    wph
    @3
    @6
    wn
    #
    wph
    @3
    @6
    wa
    #
    wn
    @3
    @26
    wi
    wph
    @2
    c0
    wcel
    #
    @27
    @2
    noel
    @27
    @2
    cA
    cB
    cin
    #
    wcel
    wph
    @28
    @2
    cA
    cB
    elin
    wph
    @29
    c0
    @2
    fsumsplit.1
    eleq2d
    syl5rbbr
    mtbii
    @3
    @6
    imnan
    sylibr
    #
    imp
    iffalsed
    oveq12d
    @25
    cC
    @17
    addid1d
    eqtrd
    wph
    @6
    wa
    #
    @9
    cc0
    cC
    caddc
    co
    cC
    @31
    @4
    cc0
    @7
    cC
    caddc
    @31
    @3
    cC
    cc0
    wph
    @6
    @3
    wn
    wph
    @3
    @6
    @30
    con2d
    imp
    iffalsed
    @6
    @7
    cC
    wceq
    wph
    @6
    cC
    cc0
    iftrue
    adantl
    oveq12d
    @31
    cC
    @20
    addid2d
    eqtrd
    jaodan
    syldan
    sumeq2dv
    3eqtr2rd
end
