include "wcel.mm"
include "cc0.mm"
include "cs1.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "s1val.mm"
include "fveq1d.mm"
include "cn0.mm"
include "wceq.mm"
include "0nn0.mm"
include "fvsng.mm"
include "mpan.mm"
include "eqtrd.mm"

theorem s1fv
  let cA: class A
  let cB: class B


  assert |- ( A e. B -> ( <" A "> ` 0 ) = A )

  proof
    cA
    cB
    wcel
    #
    cc0
    cA
    cs1
    #
    cfv
    cc0
    cc0
    cA
    cop
    csn
    #
    cfv
    #
    cA
    @0
    cc0
    @1
    @2
    cA
    cB
    s1val
    fveq1d
    cc0
    cn0
    wcel
    @0
    @3
    cA
    wceq
    0nn0
    cc0
    cA
    cn0
    cB
    fvsng
    mpan
    eqtrd
end
