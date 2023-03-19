include "wceq.mm"
include "whe.mm"
include "wb.mm"
include "eqid.mm"
include "heeq12.mm"
include "mpan.mm"

theorem heeq2
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( A = B -> ( R hereditary A <-> R hereditary B ) )

  proof
    cR
    cR
    wceq
    cA
    cB
    wceq
    cA
    cR
    whe
    cB
    cR
    whe
    wb
    cR
    eqid
    cA
    cB
    cR
    cR
    heeq12
    mpan
end
