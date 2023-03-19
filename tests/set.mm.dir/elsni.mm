include "csn.mm"
include "wcel.mm"
include "wceq.mm"
include "elsng.mm"
include "ibi.mm"

theorem elsni
  let cA: class A
  let cB: class B


  assert |- ( A e. { B } -> A = B )

  proof
    cA
    cB
    csn
    #
    wcel
    cA
    cB
    wceq
    cA
    cB
    @0
    elsng
    ibi
end
