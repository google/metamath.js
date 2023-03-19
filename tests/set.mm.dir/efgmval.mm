include "c2o.mm"
include "cv.mm"
include "c1o.mm"
include "cdif.mm"
include "cop.mm"
include "opeq1.mm"
include "wceq.mm"
include "difeq2.mm"
include "opeq2d.mm"
include "cmpt2.mm"
include "cbvmpt2v.mm"
include "eqtri.mm"
include "opex.mm"
include "ovmpt2.mm"

theorem efgmval
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cI: class I
  let cM: class M
  let va: setvar a
  let vb: setvar b
  assume efgmval.m: |- M = ( y e. I , z e. 2o |-> <. y , ( 1o \ z ) >. )

  disjoint y z
  disjoint I y
  disjoint I z
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  disjoint a y
  disjoint a z
  disjoint I a
  disjoint b y
  disjoint b z
  disjoint I b
  disjoint M a
  disjoint M b
  assert |- ( ( A e. I /\ B e. 2o ) -> ( A M B ) = <. A , ( 1o \ B ) >. )

  proof
    va
    vb
    cA
    cB
    cI
    c2o
    va
    cv
    #
    c1o
    vb
    cv
    #
    cdif
    #
    cop
    #
    cA
    c1o
    cB
    cdif
    #
    cop
    cM
    cA
    @2
    cop
    @0
    cA
    @2
    opeq1
    @1
    cB
    wceq
    @2
    @4
    cA
    @1
    cB
    c1o
    difeq2
    opeq2d
    cM
    vy
    vz
    cI
    c2o
    vy
    cv
    #
    c1o
    vz
    cv
    #
    cdif
    #
    cop
    #
    cmpt2
    va
    vb
    cI
    c2o
    @3
    cmpt2
    efgmval.m
    vy
    vz
    va
    vb
    cI
    c2o
    @8
    @3
    @0
    @7
    cop
    @5
    @0
    @7
    opeq1
    @6
    @1
    wceq
    @7
    @2
    @0
    @6
    @1
    c1o
    difeq2
    opeq2d
    cbvmpt2v
    eqtri
    cA
    @4
    opex
    ovmpt2
end
