include "ctp.mm"
include "csu.mm"
include "cpr.mm"
include "csn.mm"
include "caddc.mm"
include "co.mm"
include "wcel.mm"
include "wn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "necomd.mm"
include "nelprd.mm"
include "disjsn.mm"
include "sylibr.mm"
include "cun.mm"
include "df-tp.mm"
include "a1i.mm"
include "cfn.mm"
include "tpfi.mm"
include "cc.mm"
include "wral.mm"
include "w3a.mm"
include "wb.mm"
include "cv.mm"
include "eleq1d.mm"
include "raltpg.mm"
include "syl.mm"
include "mpbird.mm"
include "r19.21bi.mm"
include "fsumsplit.mm"
include "wa.mm"
include "3simpa.mm"
include "sumpr.mm"
include "simp3d.mm"
include "sumsn.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "eqtrd.mm"

theorem sumtp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  assume sumtp.e: |- ( k = A -> D = E )
  assume sumtp.f: |- ( k = B -> D = F )
  assume sumtp.g: |- ( k = C -> D = G )
  assume sumtp.c: |- ( ph -> ( E e. CC /\ F e. CC /\ G e. CC ) )
  assume sumtp.v: |- ( ph -> ( A e. V /\ B e. W /\ C e. X ) )
  assume sumtp.1: |- ( ph -> A =/= B )
  assume sumtp.2: |- ( ph -> A =/= C )
  assume sumtp.3: |- ( ph -> B =/= C )

  disjoint A k
  disjoint B k
  disjoint C k
  disjoint E k
  disjoint F k
  disjoint G k
  disjoint k ph
  disjoint V k
  disjoint W k
  disjoint X k
  assert |- ( ph -> sum_ k e. { A , B , C } D = ( ( E + F ) + G ) )

  proof
    wph
    cA
    cB
    cC
    ctp
    #
    cD
    vk
    csu
    cA
    cB
    cpr
    #
    cD
    vk
    csu
    #
    cC
    csn
    #
    cD
    vk
    csu
    #
    caddc
    co
    cE
    cF
    caddc
    co
    #
    cG
    caddc
    co
    wph
    @1
    @3
    cD
    @0
    vk
    wph
    cC
    @1
    wcel
    wn
    @1
    @3
    cin
    c0
    wceq
    wph
    cC
    cA
    cB
    wph
    cA
    cC
    sumtp.2
    necomd
    wph
    cB
    cC
    sumtp.3
    necomd
    nelprd
    @1
    cC
    disjsn
    sylibr
    @0
    @1
    @3
    cun
    wceq
    wph
    cA
    cB
    cC
    df-tp
    a1i
    @0
    cfn
    wcel
    wph
    cA
    cB
    cC
    tpfi
    a1i
    wph
    cD
    cc
    wcel
    #
    vk
    @0
    wph
    @6
    vk
    @0
    wral
    #
    cE
    cc
    wcel
    #
    cF
    cc
    wcel
    #
    cG
    cc
    wcel
    #
    w3a
    #
    sumtp.c
    wph
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    @7
    @11
    wb
    sumtp.v
    @6
    @8
    @9
    @10
    vk
    cA
    cB
    cC
    cV
    cW
    cX
    vk
    cv
    #
    cA
    wceq
    cD
    cE
    cc
    sumtp.e
    eleq1d
    @16
    cB
    wceq
    cD
    cF
    cc
    sumtp.f
    eleq1d
    @16
    cC
    wceq
    cD
    cG
    cc
    sumtp.g
    eleq1d
    raltpg
    syl
    mpbird
    r19.21bi
    fsumsplit
    wph
    @2
    @5
    @4
    cG
    caddc
    wph
    cA
    cB
    cD
    cE
    vk
    cF
    cV
    cW
    sumtp.e
    sumtp.f
    wph
    @11
    @8
    @9
    wa
    sumtp.c
    @8
    @9
    @10
    3simpa
    syl
    wph
    @15
    @12
    @13
    wa
    sumtp.v
    @12
    @13
    @14
    3simpa
    syl
    sumtp.1
    sumpr
    wph
    @14
    @10
    @4
    cG
    wceq
    wph
    @12
    @13
    @14
    sumtp.v
    simp3d
    wph
    @8
    @9
    @10
    sumtp.c
    simp3d
    cD
    cG
    vk
    cC
    cX
    sumtp.g
    sumsn
    syl2anc
    oveq12d
    eqtrd
end
