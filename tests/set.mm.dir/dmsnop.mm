include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "csn.mm"
include "cdm.mm"
include "wceq.mm"
include "dmsnopg.mm"
include "ax-mp.mm"

theorem dmsnop
  let cA: class A
  let cB: class B
  assume dmsnop.1: |- B e. _V


  assert |- dom { <. A , B >. } = { A }

  proof
    cB
    cvv
    wcel
    cA
    cB
    cop
    csn
    cdm
    cA
    csn
    wceq
    dmsnop.1
    cA
    cB
    cvv
    dmsnopg
    ax-mp
end
