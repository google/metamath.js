include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "cmpt.mm"
include "ctsu.mm"
include "cuni.mm"
include "cesum.mm"
include "wceq.mm"
include "wal.mm"
include "wral.mm"
include "alrimi.mm"
include "cv.mm"
include "wcel.mm"
include "ex.mm"
include "ralrimi.mm"
include "mpteq12f.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "unieqd.mm"
include "df-esum.mm"
include "3eqtr4g.mm"

theorem esumeq12dvaf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  assume esumeq12dvaf.1: |- F/ k ph
  assume esumeq12dvaf.2: |- ( ph -> A = B )
  assume esumeq12dvaf.3: |- ( ( ph /\ k e. A ) -> C = D )


  assert |- ( ph -> sum* k e. A C = sum* k e. B D )

  proof
    wph
    cxrs
    cc0
    cpnf
    cicc
    co
    cress
    co
    #
    vk
    cA
    cC
    cmpt
    #
    ctsu
    co
    #
    cuni
    @0
    vk
    cB
    cD
    cmpt
    #
    ctsu
    co
    #
    cuni
    cA
    cC
    vk
    cesum
    cB
    cD
    vk
    cesum
    wph
    @2
    @4
    wph
    @1
    @3
    @0
    ctsu
    wph
    cA
    cB
    wceq
    #
    vk
    wal
    cC
    cD
    wceq
    #
    vk
    cA
    wral
    @1
    @3
    wceq
    wph
    @5
    vk
    esumeq12dvaf.1
    esumeq12dvaf.2
    alrimi
    wph
    @6
    vk
    cA
    esumeq12dvaf.1
    wph
    vk
    cv
    cA
    wcel
    @6
    esumeq12dvaf.3
    ex
    ralrimi
    vk
    cA
    cC
    cB
    cD
    mpteq12f
    syl2anc
    oveq2d
    unieqd
    cA
    cC
    vk
    df-esum
    cB
    cD
    vk
    df-esum
    3eqtr4g
end
