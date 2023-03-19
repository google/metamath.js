include "csur.mm"
include "cslt.mm"
include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "wbr.mm"
include "wo.mm"
include "wb.mm"
include "sltso.mm"
include "sotrine.mm"
include "mpan.mm"

theorem slttrine
  let cA: class A
  let cB: class B


  assert |- ( ( A e. No /\ B e. No ) -> ( A =/= B <-> ( A <s B \/ B <s A ) ) )

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
    wne
    cA
    cB
    cslt
    wbr
    cB
    cA
    cslt
    wbr
    wo
    wb
    sltso
    csur
    cA
    cB
    cslt
    sotrine
    mpan
end
