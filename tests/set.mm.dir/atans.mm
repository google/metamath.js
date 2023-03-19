include "c1.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wcel.mm"
include "cc.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "elrab2.mm"

theorem atans
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cS: class S
  let vx: setvar x
  assume atansopn.d: |- D = ( CC \ ( -oo (,] 0 ) )
  assume atansopn.s: |- S = { y e. CC | ( 1 + ( y ^ 2 ) ) e. D }

  disjoint A y
  disjoint D y
  disjoint x y
  disjoint D x
  disjoint S x
  assert |- ( A e. S <-> ( A e. CC /\ ( 1 + ( A ^ 2 ) ) e. D ) )

  proof
    c1
    vy
    cv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    cD
    wcel
    c1
    cA
    c2
    cexp
    co
    #
    caddc
    co
    #
    cD
    wcel
    vy
    cA
    cc
    cS
    @0
    cA
    wceq
    #
    @2
    @4
    cD
    @5
    @1
    @3
    c1
    caddc
    @0
    cA
    c2
    cexp
    oveq1
    oveq2d
    eleq1d
    atansopn.s
    elrab2
end
