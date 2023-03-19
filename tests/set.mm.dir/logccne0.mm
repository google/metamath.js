include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "w3a.mm"
include "clog.mm"
include "cfv.mm"
include "wceq.mm"
include "simp3.mm"
include "neneqd.mm"
include "wi.mm"
include "logeq0im1.mm"
include "3expia.mm"
include "3adant3.mm"
include "mtod.mm"
include "neqned.mm"

theorem logccne0
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 /\ A =/= 1 ) -> ( log ` A ) =/= 0 )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cA
    c1
    wne
    #
    w3a
    #
    cA
    clog
    cfv
    #
    cc0
    @3
    @4
    cc0
    wceq
    #
    cA
    c1
    wceq
    #
    @3
    cA
    c1
    @0
    @1
    @2
    simp3
    neneqd
    @0
    @1
    @5
    @6
    wi
    @2
    @0
    @1
    @5
    @6
    cA
    logeq0im1
    3expia
    3adant3
    mtod
    neqned
end
