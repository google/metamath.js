include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "cop.mm"
include "wceq.mm"
include "xpsng.mm"
include "mp2an.mm"

theorem xpsn
  let cA: class A
  let cB: class B
  assume xpsn.1: |- A e. _V
  assume xpsn.2: |- B e. _V


  assert |- ( { A } X. { B } ) = { <. A , B >. }

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    csn
    cB
    csn
    cxp
    cA
    cB
    cop
    csn
    wceq
    xpsn.1
    xpsn.2
    cA
    cB
    cvv
    cvv
    xpsng
    mp2an
end
