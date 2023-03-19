include "csur.mm"
include "cslt.mm"
include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wceq.mm"
include "w3o.mm"
include "sltso.mm"
include "solin.mm"
include "mpan.mm"

theorem sltlin
  let cA: class A
  let cB: class B


  assert |- ( ( A e. No /\ B e. No ) -> ( A <s B \/ A = B \/ B <s A ) )

  proof
    csur
    cslt
    wor
    cA
    csur
    wcel
    cB
    csur
    wcel
    wa
    cA
    cB
    cslt
    wbr
    cA
    cB
    wceq
    cB
    cA
    cslt
    wbr
    w3o
    sltso
    csur
    cA
    cB
    cslt
    solin
    mpan
end
