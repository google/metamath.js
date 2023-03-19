include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cn0.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cdiv.mm"
include "wceq.mm"
include "negneg.mm"
include "3ad2ant2.mm"
include "oveq2d.mm"
include "expneg.mm"
include "3adant2.mm"
include "eqtr3d.mm"

theorem expneg2
  let cA: class A
  let cN: class N


  assert |- ( ( A e. CC /\ N e. CC /\ -u N e. NN0 ) -> ( A ^ N ) = ( 1 / ( A ^ -u N ) ) )

  proof
    cA
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    cN
    cneg
    #
    cn0
    wcel
    #
    w3a
    #
    cA
    @2
    cneg
    #
    cexp
    co
    #
    cA
    cN
    cexp
    co
    c1
    cA
    @2
    cexp
    co
    cdiv
    co
    #
    @4
    @5
    cN
    cA
    cexp
    @1
    @0
    @5
    cN
    wceq
    @3
    cN
    negneg
    3ad2ant2
    oveq2d
    @0
    @3
    @6
    @7
    wceq
    @1
    cA
    @2
    expneg
    3adant2
    eqtr3d
end
