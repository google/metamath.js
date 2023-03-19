include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "csn.mm"
include "wfun.mm"
include "funsng.mm"
include "mpan.mm"

theorem bnj519
  let cA: class A
  let cB: class B
  assume bnj519.1: |- A e. _V


  assert |- ( B e. _V -> Fun { <. A , B >. } )

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
    wfun
    bnj519.1
    cA
    cB
    cvv
    cvv
    funsng
    mpan
end
