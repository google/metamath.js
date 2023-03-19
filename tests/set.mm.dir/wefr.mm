include "wwe.mm"
include "wfr.mm"
include "wor.mm"
include "df-we.mm"
include "simplbi.mm"

theorem wefr
  let cA: class A
  let cR: class R


  assert |- ( R We A -> R Fr A )

  proof
    cA
    cR
    wwe
    cA
    cR
    wfr
    cA
    cR
    wor
    cA
    cR
    df-we
    simplbi
end
