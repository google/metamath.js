include "cv.mm"
include "c1o.mm"
include "cdif.mm"
include "cop.mm"
include "c2o.mm"
include "cxp.mm"
include "wcel.mm"
include "wral.mm"
include "wf.mm"
include "2oconcl.mm"
include "opelxpi.mm"
include "sylan2.mm"
include "rgen2.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem efgmf
  let vy: setvar y
  let vz: setvar z
  let cI: class I
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let cA: class A
  let cB: class B
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
  assert |- M : ( I X. 2o ) --> ( I X. 2o )

  proof
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
    cI
    c2o
    cxp
    #
    wcel
    #
    vz
    c2o
    wral
    vy
    cI
    wral
    @4
    @4
    cM
    wf
    @5
    vy
    vz
    cI
    c2o
    @1
    c2o
    wcel
    @0
    cI
    wcel
    @2
    c2o
    wcel
    @5
    @1
    2oconcl
    @0
    @2
    cI
    c2o
    opelxpi
    sylan2
    rgen2
    vy
    vz
    cI
    c2o
    @3
    @4
    cM
    efgmval.m
    fmpt2
    mpbi
end
