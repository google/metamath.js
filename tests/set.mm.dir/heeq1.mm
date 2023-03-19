include "wceq.mm"
include "whe.mm"
include "wb.mm"
include "eqid.mm"
include "heeq12.mm"
include "mpan2.mm"

theorem heeq1
  let cA: class A
  let cR: class R
  let cS: class S


  assert |- ( R = S -> ( R hereditary A <-> S hereditary A ) )

  proof
    cR
    cS
    wceq
    cA
    cA
    wceq
    cA
    cR
    whe
    cA
    cS
    whe
    wb
    cA
    eqid
    cA
    cA
    cR
    cS
    heeq12
    mpan2
end
