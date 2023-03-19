include "cpr.mm"
include "csu.mm"
include "csn.mm"
include "caddc.mm"
include "co.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "disjsn2.mm"
include "syl.mm"
include "cun.mm"
include "df-pr.mm"
include "a1i.mm"
include "cfn.mm"
include "wcel.mm"
include "prfi.mm"
include "cc.mm"
include "wral.mm"
include "wa.mm"
include "wb.mm"
include "cv.mm"
include "eleq1d.mm"
include "ralprg.mm"
include "mpbird.mm"
include "r19.21bi.mm"
include "fsumsplit.mm"
include "simpld.mm"
include "sumsn.mm"
include "syl2anc.mm"
include "simprd.mm"
include "oveq12d.mm"
include "eqtrd.mm"

theorem sumpr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cE: class E
  let cV: class V
  let cW: class W
  assume sumpr.1: |- ( k = A -> C = D )
  assume sumpr.2: |- ( k = B -> C = E )
  assume sumpr.3: |- ( ph -> ( D e. CC /\ E e. CC ) )
  assume sumpr.4: |- ( ph -> ( A e. V /\ B e. W ) )
  assume sumpr.5: |- ( ph -> A =/= B )

  disjoint A k
  disjoint B k
  disjoint D k
  disjoint E k
  disjoint k ph
  disjoint V k
  disjoint W k
  assert |- ( ph -> sum_ k e. { A , B } C = ( D + E ) )

  proof
    wph
    cA
    cB
    cpr
    #
    cC
    vk
    csu
    cA
    csn
    #
    cC
    vk
    csu
    #
    cB
    csn
    #
    cC
    vk
    csu
    #
    caddc
    co
    cD
    cE
    caddc
    co
    wph
    @1
    @3
    cC
    @0
    vk
    wph
    cA
    cB
    wne
    @1
    @3
    cin
    c0
    wceq
    sumpr.5
    cA
    cB
    disjsn2
    syl
    @0
    @1
    @3
    cun
    wceq
    wph
    cA
    cB
    df-pr
    a1i
    @0
    cfn
    wcel
    wph
    cA
    cB
    prfi
    a1i
    wph
    cC
    cc
    wcel
    #
    vk
    @0
    wph
    @5
    vk
    @0
    wral
    #
    cD
    cc
    wcel
    #
    cE
    cc
    wcel
    #
    wa
    #
    sumpr.3
    wph
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    @6
    @9
    wb
    sumpr.4
    @5
    @7
    @8
    vk
    cA
    cB
    cV
    cW
    vk
    cv
    #
    cA
    wceq
    cC
    cD
    cc
    sumpr.1
    eleq1d
    @12
    cB
    wceq
    cC
    cE
    cc
    sumpr.2
    eleq1d
    ralprg
    syl
    mpbird
    r19.21bi
    fsumsplit
    wph
    @2
    cD
    @4
    cE
    caddc
    wph
    @10
    @7
    @2
    cD
    wceq
    wph
    @10
    @11
    sumpr.4
    simpld
    wph
    @7
    @8
    sumpr.3
    simpld
    cC
    cD
    vk
    cA
    cV
    sumpr.1
    sumsn
    syl2anc
    wph
    @11
    @8
    @4
    cE
    wceq
    wph
    @10
    @11
    sumpr.4
    simprd
    wph
    @7
    @8
    sumpr.3
    simprd
    cC
    cE
    vk
    cB
    cW
    sumpr.2
    sumsn
    syl2anc
    oveq12d
    eqtrd
end
