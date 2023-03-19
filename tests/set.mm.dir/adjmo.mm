include "chil.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wmo.mm"
include "wi.mm"
include "wal.mm"
include "r19.26-2.mm"
include "eqtr2.mm"
include "2ralimi.mm"
include "sylbir.mm"
include "hoeq1.mm"
include "biimpa.mm"
include "sylan2.mm"
include "an4s.mm"
include "gen2.mm"
include "feq1.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "mo4.mm"
include "mpbir.mm"

theorem adjmo
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cT: class T
  let vz: setvar z
  let cS: class S
  let vv: setvar v

  disjoint x y
  disjoint u x
  disjoint u y
  disjoint T u
  disjoint T x
  disjoint T y
  disjoint x z
  disjoint S x
  disjoint y z
  disjoint S y
  disjoint S z
  disjoint u v
  disjoint u z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint T v
  disjoint T z
  assert |- E* u ( u : ~H --> ~H /\ A. x e. ~H A. y e. ~H ( x .ih ( T ` y ) ) = ( ( u ` x ) .ih y ) )

  proof
    chil
    chil
    vu
    cv
    #
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cT
    cfv
    csp
    co
    #
    @2
    @0
    cfv
    #
    @3
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
    #
    wa
    #
    vu
    wmo
    @9
    chil
    chil
    vv
    cv
    #
    wf
    #
    @4
    @2
    @10
    cfv
    #
    @3
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
    #
    wa
    #
    wa
    @0
    @10
    wceq
    #
    wi
    #
    vv
    wal
    vu
    wal
    @18
    vu
    vv
    @1
    @11
    @8
    @15
    @17
    @8
    @15
    wa
    #
    @1
    @11
    wa
    #
    @6
    @13
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    @17
    @19
    @7
    @14
    wa
    #
    vy
    chil
    wral
    vx
    chil
    wral
    @22
    @7
    @14
    vx
    vy
    chil
    chil
    r19.26-2
    @23
    @21
    vx
    vy
    chil
    chil
    @4
    @6
    @13
    eqtr2
    2ralimi
    sylbir
    @20
    @22
    @17
    vx
    vy
    @0
    @10
    hoeq1
    biimpa
    sylan2
    an4s
    gen2
    @9
    @16
    vu
    vv
    @17
    @1
    @11
    @8
    @15
    chil
    chil
    @0
    @10
    feq1
    @17
    @7
    @14
    vx
    vy
    chil
    chil
    @17
    @6
    @13
    @4
    @17
    @5
    @12
    @3
    csp
    @2
    @0
    @10
    fveq1
    oveq1d
    eqeq2d
    2ralbidv
    anbi12d
    mo4
    mpbir
end
