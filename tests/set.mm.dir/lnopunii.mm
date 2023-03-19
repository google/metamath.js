include "cuo.mm"
include "wcel.mm"
include "chil.mm"
include "wfo.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "c0v.mm"
include "cif.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "ifhvhv0.mm"
include "lnopunilem2.mm"
include "dedth2h.mm"
include "rgen2a.mm"
include "elunop.mm"
include "mpbir2an.mm"

theorem lnopunii
  let vx: setvar x
  let cT: class T
  let vy: setvar y
  assume lnopuni.1: |- T e. LinOp
  assume lnopuni.2: |- T : ~H -onto-> ~H
  assume lnopuni.3: |- A. x e. ~H ( normh ` ( T ` x ) ) = ( normh ` x )

  disjoint T x
  disjoint x y
  disjoint T y
  assert |- T e. UniOp

  proof
    cT
    cuo
    wcel
    chil
    chil
    cT
    wfo
    vx
    cv
    #
    cT
    cfv
    #
    vy
    cv
    #
    cT
    cfv
    #
    csp
    co
    #
    @0
    @2
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    lnopuni.2
    @6
    vx
    vy
    chil
    @0
    chil
    wcel
    #
    @2
    chil
    wcel
    #
    @6
    @7
    @0
    c0v
    cif
    #
    cT
    cfv
    #
    @3
    csp
    co
    #
    @9
    @2
    csp
    co
    #
    wceq
    @10
    @8
    @2
    c0v
    cif
    #
    cT
    cfv
    #
    csp
    co
    #
    @9
    @13
    csp
    co
    #
    wceq
    @0
    @2
    c0v
    c0v
    @0
    @9
    wceq
    #
    @4
    @11
    @5
    @12
    @17
    @1
    @10
    @3
    csp
    @0
    @9
    cT
    fveq2
    oveq1d
    @0
    @9
    @2
    csp
    oveq1
    eqeq12d
    @2
    @13
    wceq
    #
    @11
    @15
    @12
    @16
    @18
    @3
    @14
    @10
    csp
    @2
    @13
    cT
    fveq2
    oveq2d
    @2
    @13
    @9
    csp
    oveq2
    eqeq12d
    vx
    @9
    @13
    cT
    lnopuni.1
    lnopuni.3
    @0
    ifhvhv0
    @2
    ifhvhv0
    lnopunilem2
    dedth2h
    rgen2a
    vx
    vy
    cT
    elunop
    mpbir2an
end
