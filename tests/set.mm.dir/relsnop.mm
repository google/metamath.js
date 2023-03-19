include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "csn.mm"
include "wrel.mm"
include "relsnopg.mm"
include "mp2an.mm"

theorem relsnop
  let cA: class A
  let cB: class B
  assume relsn.1: |- A e. _V
  assume relsnop.2: |- B e. _V


  assert |- Rel { <. A , B >. }

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cop
    csn
    wrel
    relsn.1
    relsnop.2
    cA
    cB
    cvv
    cvv
    relsnopg
    mp2an
end
