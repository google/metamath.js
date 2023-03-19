include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "csn.mm"
include "wfn.mm"
include "fnsng.mm"
include "mp2an.mm"

theorem fnsn
  let cA: class A
  let cB: class B
  assume fnsn.1: |- A e. _V
  assume fnsn.2: |- B e. _V


  assert |- { <. A , B >. } Fn { A }

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
    cA
    csn
    wfn
    fnsn.1
    fnsn.2
    cA
    cB
    cvv
    cvv
    fnsng
    mp2an
end
