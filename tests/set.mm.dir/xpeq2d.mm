include "wceq.mm"
include "cxp.mm"
include "xpeq2.mm"
include "syl.mm"

theorem xpeq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume xpeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C X. A ) = ( C X. B ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    cxp
    cC
    cB
    cxp
    wceq
    xpeq1d.1
    cA
    cB
    cC
    xpeq2
    syl
end
