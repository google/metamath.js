include "wcel.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "ciun.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "cvv.mm"
include "abrexexg.mm"
include "vex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "cardidm.mm"
include "fveq2.mm"
include "id.mm"
include "3eqtr4a.mm"
include "rexlimivw.mm"
include "sylbi.mm"
include "rgen.mm"
include "carduni.mm"
include "mpisyl.mm"
include "fvex.mm"
include "dfiun2.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "adantr.mm"
include "iuneq2.mm"
include "adantl.mm"
include "fveq2d.mm"
include "3eqtr3d.mm"
include "ex.mm"

theorem cardiun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  assert |- ( A e. V -> ( A. x e. A ( card ` B ) = B -> ( card ` U_ x e. A B ) = U_ x e. A B ) )

  proof
    cA
    cV
    wcel
    #
    cB
    ccrd
    cfv
    #
    cB
    wceq
    vx
    cA
    wral
    #
    vx
    cA
    cB
    ciun
    #
    ccrd
    cfv
    #
    @3
    wceq
    @0
    @2
    wa
    #
    vx
    cA
    @1
    ciun
    #
    ccrd
    cfv
    #
    @6
    @4
    @3
    @0
    @7
    @6
    wceq
    @2
    @0
    vz
    cv
    #
    @1
    wceq
    #
    vx
    cA
    wrex
    #
    vz
    cab
    #
    cuni
    #
    ccrd
    cfv
    #
    @12
    @7
    @6
    @0
    @11
    cvv
    wcel
    vy
    cv
    #
    ccrd
    cfv
    #
    @14
    wceq
    #
    vy
    @11
    wral
    @13
    @12
    wceq
    vx
    vz
    cA
    @1
    cV
    abrexexg
    @16
    vy
    @11
    @14
    @11
    wcel
    @14
    @1
    wceq
    #
    vx
    cA
    wrex
    #
    @16
    @10
    @18
    vz
    @14
    vy
    vex
    @8
    @14
    wceq
    @9
    @17
    vx
    cA
    @8
    @14
    @1
    eqeq1
    rexbidv
    elab
    @17
    @16
    vx
    cA
    @17
    @1
    ccrd
    cfv
    @1
    @15
    @14
    cB
    cardidm
    @14
    @1
    ccrd
    fveq2
    @17
    id
    3eqtr4a
    rexlimivw
    sylbi
    rgen
    vy
    @11
    cvv
    carduni
    mpisyl
    @6
    @12
    ccrd
    vx
    vz
    cA
    @1
    cB
    ccrd
    fvex
    dfiun2
    #
    fveq2i
    @19
    3eqtr4g
    adantr
    @5
    @6
    @3
    ccrd
    @2
    @6
    @3
    wceq
    @0
    vx
    cA
    @1
    cB
    iuneq2
    adantl
    #
    fveq2d
    @20
    3eqtr3d
    ex
end
