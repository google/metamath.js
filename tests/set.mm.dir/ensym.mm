include "cen.mm"
include "wbr.mm"
include "ensymb.mm"
include "biimpi.mm"

theorem ensym
  let cA: class A
  let cB: class B


  assert |- ( A ~~ B -> B ~~ A )

  proof
    cA
    cB
    cen
    wbr
    cB
    cA
    cen
    wbr
    cA
    cB
    ensymb
    biimpi
end
