include "wceq.mm"
include "cxrn.mm"
include "xrneq1.mm"
include "syl.mm"

theorem xrneq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume xrneq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( A |X. C ) = ( B |X. C ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    cxrn
    cB
    cC
    cxrn
    wceq
    xrneq1d.1
    cA
    cB
    cC
    xrneq1
    syl
end
