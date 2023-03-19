include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "wceq.mm"
include "wa.mm"
include "1z.mm"
include "expaddz.mm"
include "mpanr2.mm"
include "3impa.mm"
include "exp1.mm"
include "3ad2ant1.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem expp1z
  let cA: class A
  let cN: class N


  assert |- ( ( A e. CC /\ A =/= 0 /\ N e. ZZ ) -> ( A ^ ( N + 1 ) ) = ( ( A ^ N ) x. A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cA
    cN
    c1
    caddc
    co
    cexp
    co
    #
    cA
    cN
    cexp
    co
    #
    cA
    c1
    cexp
    co
    #
    cmul
    co
    #
    @5
    cA
    cmul
    co
    @0
    @1
    @2
    @4
    @7
    wceq
    #
    @0
    @1
    wa
    @2
    c1
    cz
    wcel
    @8
    1z
    cA
    cN
    c1
    expaddz
    mpanr2
    3impa
    @3
    @6
    cA
    @5
    cmul
    @0
    @1
    @6
    cA
    wceq
    @2
    cA
    exp1
    3ad2ant1
    oveq2d
    eqtrd
end
