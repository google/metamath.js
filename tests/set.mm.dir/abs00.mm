include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "absrpcl.mm"
include "rpne0d.mm"
include "ex.mm"
include "necon4d.mm"
include "fveq2.mm"
include "abs0.mm"
include "syl6eq.mm"
include "impbid1.mm"

theorem abs00
  let cA: class A


  assert |- ( A e. CC -> ( ( abs ` A ) = 0 <-> A = 0 ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cabs
    cfv
    #
    cc0
    wceq
    cA
    cc0
    wceq
    #
    @0
    cA
    cc0
    @1
    cc0
    @0
    cA
    cc0
    wne
    #
    @1
    cc0
    wne
    @0
    @3
    wa
    @1
    cA
    absrpcl
    rpne0d
    ex
    necon4d
    @2
    @1
    cc0
    cabs
    cfv
    cc0
    cA
    cc0
    cabs
    fveq2
    abs0
    syl6eq
    impbid1
end
