include "cho.mm"
include "wcel.mm"
include "chil.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wf.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "df-hmop.mm"
include "elrab2.mm"
include "ax-hilex.mm"
include "elmap.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem elhmop
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint T x
  disjoint T y
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint T t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint T u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint T w
  disjoint x z
  disjoint y z
  disjoint T z
  assert |- ( T e. HrmOp <-> ( T : ~H --> ~H /\ A. x e. ~H A. y e. ~H ( x .ih ( T ` y ) ) = ( ( T ` x ) .ih y ) ) )

  proof
    cT
    cho
    wcel
    cT
    chil
    chil
    cmap
    co
    #
    wcel
    #
    vx
    cv
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
    @2
    cT
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
    chil
    chil
    cT
    wf
    #
    @9
    wa
    @2
    @3
    vt
    cv
    #
    cfv
    #
    csp
    co
    #
    @2
    @11
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
    @9
    vt
    cT
    @0
    cho
    @11
    cT
    wceq
    #
    @16
    @8
    vx
    vy
    chil
    chil
    @17
    @13
    @5
    @15
    @7
    @17
    @12
    @4
    @2
    csp
    @3
    @11
    cT
    fveq1
    oveq2d
    @17
    @14
    @6
    @3
    csp
    @2
    @11
    cT
    fveq1
    oveq1d
    eqeq12d
    2ralbidv
    vx
    vy
    vt
    df-hmop
    elrab2
    @1
    @10
    @9
    chil
    chil
    cT
    ax-hilex
    ax-hilex
    elmap
    anbi1i
    bitri
end
