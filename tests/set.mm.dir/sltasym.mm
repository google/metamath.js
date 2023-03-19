include "csur.mm"
include "cslt.mm"
include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "sltso.mm"
include "soasym.mm"
include "mpan.mm"

theorem sltasym
  let cA: class A
  let cB: class B


  assert |- ( ( A e. No /\ B e. No ) -> ( A <s B -> -. B <s A ) )

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
    cB
    cA
    cslt
    wbr
    wn
    wi
    sltso
    csur
    cslt
    cA
    cB
    soasym
    mpan
end
