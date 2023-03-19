include "wceq.mm"
include "cxrn.mm"
include "xrneq2.mm"
include "syl.mm"

theorem xrneq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume xrneq2d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C |X. A ) = ( C |X. B ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    cxrn
    cC
    cB
    cxrn
    wceq
    xrneq2d.1
    cA
    cB
    cC
    xrneq2
    syl
end
