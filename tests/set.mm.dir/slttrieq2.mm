include "csur.mm"
include "cslt.mm"
include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wbr.mm"
include "wn.mm"
include "wb.mm"
include "sltso.mm"
include "sotrieq2.mm"
include "mpan.mm"

theorem slttrieq2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. No /\ B e. No ) -> ( A = B <-> ( -. A <s B /\ -. B <s A ) ) )

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
    wceq
    cA
    cB
    cslt
    wbr
    wn
    cB
    cA
    cslt
    wbr
    wn
    wa
    wb
    sltso
    csur
    cA
    cB
    cslt
    sotrieq2
    mpan
end
