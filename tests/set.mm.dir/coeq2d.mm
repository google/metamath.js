include "wceq.mm"
include "ccom.mm"
include "coeq2.mm"
include "syl.mm"

theorem coeq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume coeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C o. A ) = ( C o. B ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    ccom
    cC
    cB
    ccom
    wceq
    coeq1d.1
    cA
    cB
    cC
    coeq2
    syl
end
