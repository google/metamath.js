include "wceq.mm"
include "ccom.mm"
include "coeq1.mm"
include "syl.mm"

theorem coeq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume coeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( A o. C ) = ( B o. C ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    ccom
    cB
    cC
    ccom
    wceq
    coeq1d.1
    cA
    cB
    cC
    coeq1
    syl
end
