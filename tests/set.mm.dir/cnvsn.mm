include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "csn.mm"
include "ccnv.mm"
include "wceq.mm"
include "cnvsng.mm"
include "mp2an.mm"

theorem cnvsn
  let cA: class A
  let cB: class B
  assume cnvsn.1: |- A e. _V
  assume cnvsn.2: |- B e. _V


  assert |- `' { <. A , B >. } = { <. B , A >. }

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
    ccnv
    cB
    cA
    cop
    csn
    wceq
    cnvsn.1
    cnvsn.2
    cA
    cB
    cvv
    cvv
    cnvsng
    mp2an
end
