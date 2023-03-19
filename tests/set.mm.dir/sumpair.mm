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
include "cv.mm"
include "wo.mm"
include "cc.mm"
include "elpri.mm"
include "wa.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "jaodan.mm"
include "sylan2.mm"
include "fsumsplit.mm"
include "nfv.mm"
include "sumsnd.mm"
include "oveq12d.mm"
include "eqtrd.mm"

theorem sumpair
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cE: class E
  let cV: class V
  let cW: class W
  assume sumpair.1: |- ( ph -> F/_ k D )
  assume sumpair.3: |- ( ph -> F/_ k E )
  assume sumupair.1: |- ( ph -> A e. V )
  assume sumupair.2: |- ( ph -> B e. W )
  assume sumupair.3: |- ( ph -> D e. CC )
  assume sumupair.4: |- ( ph -> E e. CC )
  assume sumupair.5: |- ( ph -> A =/= B )
  assume sumupair.8: |- ( ( ph /\ k = A ) -> C = D )
  assume sumupair.9: |- ( ( ph /\ k = B ) -> C = E )

  disjoint A k
  disjoint B k
  disjoint k ph
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
    sumupair.5
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
    vk
    cv
    #
    @0
    wcel
    wph
    @5
    cA
    wceq
    #
    @5
    cB
    wceq
    #
    wo
    cC
    cc
    wcel
    #
    @5
    cA
    cB
    elpri
    wph
    @6
    @8
    @7
    wph
    @6
    wa
    cC
    cD
    cc
    sumupair.8
    wph
    cD
    cc
    wcel
    @6
    sumupair.3
    adantr
    eqeltrd
    wph
    @7
    wa
    cC
    cE
    cc
    sumupair.9
    wph
    cE
    cc
    wcel
    @7
    sumupair.4
    adantr
    eqeltrd
    jaodan
    sylan2
    fsumsplit
    wph
    @2
    cD
    @4
    cE
    caddc
    wph
    cC
    cD
    vk
    cA
    cV
    sumpair.1
    wph
    vk
    nfv
    #
    sumupair.8
    sumupair.1
    sumupair.3
    sumsnd
    wph
    cC
    cE
    vk
    cB
    cW
    sumpair.3
    @9
    sumupair.9
    sumupair.2
    sumupair.4
    sumsnd
    oveq12d
    eqtrd
end
