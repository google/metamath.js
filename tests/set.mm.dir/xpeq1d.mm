include "wceq.mm"
include "cxp.mm"
include "xpeq1.mm"
include "syl.mm"

theorem xpeq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume xpeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( A X. C ) = ( B X. C ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    cxp
    cB
    cC
    cxp
    wceq
    xpeq1d.1
    cA
    cB
    cC
    xpeq1
    syl
end
