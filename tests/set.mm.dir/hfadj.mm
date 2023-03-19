include "chf.mm"
include "wcel.mm"
include "csn.mm"
include "cun.mm"
include "hfsn.mm"
include "hfun.mm"
include "sylan2.mm"

theorem hfadj
  let cA: class A
  let cB: class B


  assert |- ( ( A e. Hf /\ B e. Hf ) -> ( A u. { B } ) e. Hf )

  proof
    cB
    chf
    wcel
    cA
    chf
    wcel
    cB
    csn
    #
    chf
    wcel
    cA
    @0
    cun
    chf
    wcel
    cB
    hfsn
    cA
    @0
    hfun
    sylan2
end
