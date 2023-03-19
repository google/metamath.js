include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "csn.mm"
include "crn.mm"
include "wceq.mm"
include "rnsnopg.mm"
include "ax-mp.mm"

theorem rnsnop
  let cA: class A
  let cB: class B
  assume cnvsn.1: |- A e. _V


  assert |- ran { <. A , B >. } = { B }

  proof
    cA
    cvv
    wcel
    cA
    cB
    cop
    csn
    crn
    cB
    csn
    wceq
    cnvsn.1
    cA
    cB
    cvv
    rnsnopg
    ax-mp
end
