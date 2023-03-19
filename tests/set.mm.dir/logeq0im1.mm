include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "clog.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "ce.mm"
include "c1.mm"
include "eflog.mm"
include "3adant3.mm"
include "fveq2.mm"
include "ef0.mm"
include "syl6eq.mm"
include "3ad2ant3.mm"
include "eqtr3d.mm"

theorem logeq0im1
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 /\ ( log ` A ) = 0 ) -> A = 1 )

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
    clog
    cfv
    #
    cc0
    wceq
    #
    w3a
    @2
    ce
    cfv
    #
    cA
    c1
    @0
    @1
    @4
    cA
    wceq
    @3
    cA
    eflog
    3adant3
    @3
    @0
    @4
    c1
    wceq
    @1
    @3
    @4
    cc0
    ce
    cfv
    c1
    @2
    cc0
    ce
    fveq2
    ef0
    syl6eq
    3ad2ant3
    eqtr3d
end
