include "cun.mm"
include "csu.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cif.mm"
include "caddc.mm"
include "co.mm"
include "wss.mm"
include "cc.mm"
include "wral.mm"
include "cuz.mm"
include "cfv.mm"
include "cfn.mm"
include "wo.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "eqimssi.mm"
include "a1i.mm"
include "orcd.mm"
include "sumss2.mm"
include "syl21anc.mm"
include "wa.mm"
include "iftrue.mm"
include "adantl.mm"
include "elun1.mm"
include "sylan2.mm"
include "eqeltrd.mm"
include "wn.mm"
include "iffalse.mm"
include "0cn.mm"
include "syl6eqel.mm"
include "pm2.61dan.mm"
include "adantr.mm"
include "elun2.mm"
include "isumadd.mm"
include "addid1d.mm"
include "wi.mm"
include "c0.mm"
include "noel.mm"
include "cin.mm"
include "elin.mm"
include "eleq2d.mm"
include "syl5rbbr.mm"
include "mtbii.mm"
include "imnan.mm"
include "sylibr.mm"
include "imp.mm"
include "syl.mm"
include "oveq12d.mm"
include "3eqtr4rd.mm"
include "addid2d.mm"
include "oveq1d.mm"
include "wb.mm"
include "biorf.mm"
include "elun.mm"
include "syl6rbbr.mm"
include "ifbid.mm"
include "sumeq2sdv.mm"
include "unssad.mm"
include "unssbd.mm"
include "eqtr4d.mm"

theorem sumsplit
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  assume sumsplit.1: |- Z = ( ZZ>= ` M )
  assume sumsplit.2: |- ( ph -> M e. ZZ )
  assume sumsplit.3: |- ( ph -> ( A i^i B ) = (/) )
  assume sumsplit.4: |- ( ph -> ( A u. B ) C_ Z )
  assume sumsplit.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = if ( k e. A , C , 0 ) )
  assume sumsplit.6: |- ( ( ph /\ k e. Z ) -> ( G ` k ) = if ( k e. B , C , 0 ) )
  assume sumsplit.7: |- ( ( ph /\ k e. ( A u. B ) ) -> C e. CC )
  assume sumsplit.8: |- ( ph -> seq M ( + , F ) e. dom ~~> )
  assume sumsplit.9: |- ( ph -> seq M ( + , G ) e. dom ~~> )

  disjoint A k
  disjoint B k
  disjoint F k
  disjoint G k
  disjoint M k
  disjoint k ph
  disjoint Z k
  assert |- ( ph -> sum_ k e. ( A u. B ) C = ( sum_ k e. A C + sum_ k e. B C ) )

  proof
    wph
    cA
    cB
    cun
    #
    cC
    vk
    csu
    #
    cZ
    vk
    cv
    #
    @0
    wcel
    #
    cC
    cc0
    cif
    #
    vk
    csu
    #
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
    #
    wph
    @0
    cZ
    wss
    cC
    cc
    wcel
    #
    vk
    @0
    wral
    cZ
    cM
    cuz
    cfv
    #
    wss
    #
    cZ
    cfn
    wcel
    #
    wo
    #
    @1
    @5
    wceq
    sumsplit.4
    wph
    @9
    vk
    @0
    sumsplit.7
    ralrimiva
    wph
    @11
    @12
    @11
    wph
    cZ
    @10
    sumsplit.1
    eqimssi
    a1i
    orcd
    #
    @0
    cZ
    cC
    vk
    cM
    sumss2
    syl21anc
    wph
    cZ
    @2
    cA
    wcel
    #
    cC
    cc0
    cif
    #
    @2
    cB
    wcel
    #
    cC
    cc0
    cif
    #
    caddc
    co
    #
    vk
    csu
    cZ
    @16
    vk
    csu
    #
    cZ
    @18
    vk
    csu
    #
    caddc
    co
    @5
    @8
    wph
    @16
    @18
    vk
    cF
    cG
    cM
    cZ
    sumsplit.1
    sumsplit.2
    sumsplit.5
    wph
    @16
    cc
    wcel
    #
    @2
    cZ
    wcel
    #
    wph
    @15
    @22
    wph
    @15
    wa
    #
    @16
    cC
    cc
    @15
    @16
    cC
    wceq
    wph
    @15
    cC
    cc0
    iftrue
    adantl
    #
    @15
    wph
    @3
    @9
    @2
    cA
    cB
    elun1
    #
    sumsplit.7
    sylan2
    #
    eqeltrd
    @15
    wn
    #
    @22
    wph
    @28
    @16
    cc0
    cc
    @15
    cC
    cc0
    iffalse
    #
    0cn
    syl6eqel
    adantl
    pm2.61dan
    adantr
    sumsplit.6
    wph
    @18
    cc
    wcel
    #
    @23
    wph
    @17
    @30
    wph
    @17
    wa
    @18
    cC
    cc
    @17
    @18
    cC
    wceq
    wph
    @17
    cC
    cc0
    iftrue
    adantl
    @17
    wph
    @3
    @9
    @2
    cB
    cA
    elun2
    sumsplit.7
    sylan2
    #
    eqeltrd
    @17
    wn
    #
    @30
    wph
    @32
    @18
    cc0
    cc
    @17
    cC
    cc0
    iffalse
    #
    0cn
    syl6eqel
    adantl
    pm2.61dan
    #
    adantr
    sumsplit.8
    sumsplit.9
    isumadd
    wph
    cZ
    @4
    @19
    vk
    wph
    @15
    @4
    @19
    wceq
    @24
    cC
    cc0
    caddc
    co
    cC
    @19
    @4
    @24
    cC
    @27
    addid1d
    @24
    @16
    cC
    @18
    cc0
    caddc
    @25
    @24
    @32
    @18
    cc0
    wceq
    wph
    @15
    @32
    wph
    @15
    @17
    wa
    #
    wn
    @15
    @32
    wi
    wph
    @2
    c0
    wcel
    #
    @35
    @2
    noel
    @35
    @2
    cA
    cB
    cin
    #
    wcel
    wph
    @36
    @2
    cA
    cB
    elin
    wph
    @37
    c0
    @2
    sumsplit.3
    eleq2d
    syl5rbbr
    mtbii
    @15
    @17
    imnan
    sylibr
    imp
    @33
    syl
    oveq12d
    @15
    @4
    cC
    wceq
    #
    wph
    @15
    @3
    @38
    @26
    @3
    cC
    cc0
    iftrue
    syl
    adantl
    3eqtr4rd
    wph
    @28
    wa
    #
    cc0
    @18
    caddc
    co
    #
    @18
    @19
    @4
    wph
    @40
    @18
    wceq
    @28
    wph
    @18
    @34
    addid2d
    adantr
    @39
    @16
    cc0
    @18
    caddc
    @28
    @16
    cc0
    wceq
    wph
    @29
    adantl
    oveq1d
    @39
    @3
    @17
    cC
    cc0
    @28
    @3
    @17
    wb
    wph
    @28
    @17
    @15
    @17
    wo
    @3
    @15
    @17
    biorf
    @2
    cA
    cB
    elun
    syl6rbbr
    adantl
    ifbid
    3eqtr4rd
    pm2.61dan
    sumeq2sdv
    wph
    @6
    @20
    @7
    @21
    caddc
    wph
    cA
    cZ
    wss
    @9
    vk
    cA
    wral
    @13
    @6
    @20
    wceq
    wph
    cA
    cB
    cZ
    sumsplit.4
    unssad
    wph
    @9
    vk
    cA
    @27
    ralrimiva
    @14
    cA
    cZ
    cC
    vk
    cM
    sumss2
    syl21anc
    wph
    cB
    cZ
    wss
    @9
    vk
    cB
    wral
    @13
    @7
    @21
    wceq
    wph
    cA
    cB
    cZ
    sumsplit.4
    unssbd
    wph
    @9
    vk
    cB
    @31
    ralrimiva
    @14
    cB
    cZ
    cC
    vk
    cM
    sumss2
    syl21anc
    oveq12d
    3eqtr4rd
    eqtr4d
end
