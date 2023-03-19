include "wceq.mm"
include "cxp.mm"
include "xpeq12.mm"
include "syl2anc.mm"

theorem xpeq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume xpeq1d.1: |- ( ph -> A = B )
  assume xpeq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> ( A X. C ) = ( B X. D ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cxp
    cB
    cD
    cxp
    wceq
    xpeq1d.1
    xpeq12d.2
    cA
    cB
    cC
    cD
    xpeq12
    syl2anc
end
