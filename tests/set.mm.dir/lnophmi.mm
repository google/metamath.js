include "cho.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "lnopfi.mm"
include "c0v.mm"
include "cif.mm"
include "oveq1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "ifhvhv0.mm"
include "lnophmlem2.mm"
include "dedth2h.mm"
include "rgen2a.mm"
include "elhmop.mm"
include "mpbir2an.mm"

theorem lnophmi
  let vx: setvar x
  let cT: class T
  let vy: setvar y
  let vz: setvar z
  assume lnophm.1: |- T e. LinOp
  assume lnophm.2: |- A. x e. ~H ( x .ih ( T ` x ) ) e. RR

  disjoint T x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint T y
  disjoint T z
  assert |- T e. HrmOp

  proof
    cT
    cho
    wcel
    chil
    chil
    cT
    wf
    vy
    cv
    #
    vz
    cv
    #
    cT
    cfv
    #
    csp
    co
    #
    @0
    cT
    cfv
    #
    @1
    csp
    co
    #
    wceq
    #
    vz
    chil
    wral
    vy
    chil
    wral
    cT
    lnophm.1
    lnopfi
    @6
    vy
    vz
    chil
    @0
    chil
    wcel
    #
    @1
    chil
    wcel
    #
    @6
    @7
    @0
    c0v
    cif
    #
    @2
    csp
    co
    #
    @9
    cT
    cfv
    #
    @1
    csp
    co
    #
    wceq
    @9
    @8
    @1
    c0v
    cif
    #
    cT
    cfv
    #
    csp
    co
    #
    @11
    @13
    csp
    co
    #
    wceq
    @0
    @1
    c0v
    c0v
    @0
    @9
    wceq
    #
    @3
    @10
    @5
    @12
    @0
    @9
    @2
    csp
    oveq1
    @17
    @4
    @11
    @1
    csp
    @0
    @9
    cT
    fveq2
    oveq1d
    eqeq12d
    @1
    @13
    wceq
    #
    @10
    @15
    @12
    @16
    @18
    @2
    @14
    @9
    csp
    @1
    @13
    cT
    fveq2
    oveq2d
    @1
    @13
    @11
    csp
    oveq2
    eqeq12d
    vx
    @9
    @13
    cT
    @0
    ifhvhv0
    @1
    ifhvhv0
    lnophm.1
    lnophm.2
    lnophmlem2
    dedth2h
    rgen2a
    vy
    vz
    cT
    elhmop
    mpbir2an
end
