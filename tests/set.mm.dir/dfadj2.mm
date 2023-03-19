include "cado.mm"
include "chil.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "copab.mm"
include "df-adjh.mm"
include "wa.mm"
include "adjsym.mm"
include "eqcom.mm"
include "2ralbii.mm"
include "syl6rbbr.mm"
include "pm5.32i.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "opabbii.mm"
include "eqtri.mm"

theorem dfadj2
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vt: setvar t
  let vw: setvar w
  let vz: setvar z
  let cT: class T

  disjoint t u
  disjoint t x
  disjoint t y
  disjoint u x
  disjoint u y
  disjoint x y
  disjoint t w
  disjoint t z
  disjoint T t
  disjoint u w
  disjoint u z
  disjoint T u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint T w
  disjoint x z
  disjoint T x
  disjoint y z
  disjoint T y
  disjoint T z
  assert |- adjh = { <. t , u >. | ( t : ~H --> ~H /\ u : ~H --> ~H /\ A. x e. ~H A. y e. ~H ( x .ih ( t ` y ) ) = ( ( u ` x ) .ih y ) ) }

  proof
    cado
    chil
    chil
    vt
    cv
    #
    wf
    #
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
    @0
    cfv
    vy
    cv
    #
    csp
    co
    #
    @4
    @5
    @2
    cfv
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
    w3a
    #
    vt
    vu
    copab
    @1
    @3
    @4
    @5
    @0
    cfv
    csp
    co
    @4
    @2
    cfv
    @5
    csp
    co
    wceq
    vy
    chil
    wral
    vx
    chil
    wral
    #
    w3a
    #
    vt
    vu
    copab
    vx
    vy
    vu
    vt
    df-adjh
    @10
    @12
    vt
    vu
    @1
    @3
    wa
    #
    @9
    wa
    @13
    @11
    wa
    @10
    @12
    @13
    @9
    @11
    @13
    @11
    @7
    @6
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    @9
    vx
    vy
    @0
    @2
    adjsym
    @8
    @14
    vx
    vy
    chil
    chil
    @6
    @7
    eqcom
    2ralbii
    syl6rbbr
    pm5.32i
    @1
    @3
    @9
    df-3an
    @1
    @3
    @11
    df-3an
    3bitr4i
    opabbii
    eqtri
end
