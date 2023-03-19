include "wceq.mm"
include "cxrn.mm"
include "xrneq12.mm"
include "syl2anc.mm"

theorem xrneq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume xrneq12d.1: |- ( ph -> A = B )
  assume xrneq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> ( A |X. C ) = ( B |X. D ) )

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
    cxrn
    cB
    cD
    cxrn
    wceq
    xrneq12d.1
    xrneq12d.2
    cA
    cB
    cC
    cD
    xrneq12
    syl2anc
end
