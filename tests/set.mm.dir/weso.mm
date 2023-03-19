include "wwe.mm"
include "wfr.mm"
include "wor.mm"
include "df-we.mm"
include "simprbi.mm"

theorem weso
  let cA: class A
  let cR: class R


  assert |- ( R We A -> R Or A )

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
    simprbi
end
