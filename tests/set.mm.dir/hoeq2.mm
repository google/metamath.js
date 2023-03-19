include "chil.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wb.mm"
include "ralcom.mm"
include "a1i.mm"
include "wcel.mm"
include "ffvelrn.mm"
include "hial2eq2.mm"
include "hial2eq.mm"
include "bitr4d.mm"
include "syl2an.mm"
include "anandirs.mm"
include "ralbidva.mm"
include "hoeq1.mm"
include "3bitrd.mm"

theorem hoeq2
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cT: class T
  let vz: setvar z
  let vu: setvar u
  let vv: setvar v

  disjoint x y
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint x z
  disjoint y z
  disjoint S z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint T u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint T v
  disjoint T z
  assert |- ( ( S : ~H --> ~H /\ T : ~H --> ~H ) -> ( A. x e. ~H A. y e. ~H ( x .ih ( S ` y ) ) = ( x .ih ( T ` y ) ) <-> S = T ) )

  proof
    chil
    chil
    cS
    wf
    #
    chil
    chil
    cT
    wf
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    cS
    cfv
    #
    csp
    co
    @3
    @4
    cT
    cfv
    #
    csp
    co
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    @7
    vx
    chil
    wral
    #
    vy
    chil
    wral
    #
    @5
    @3
    csp
    co
    @6
    @3
    csp
    co
    wceq
    vx
    chil
    wral
    #
    vy
    chil
    wral
    cS
    cT
    wceq
    @8
    @10
    wb
    @2
    @7
    vx
    vy
    chil
    chil
    ralcom
    a1i
    @2
    @9
    @11
    vy
    chil
    @0
    @1
    @4
    chil
    wcel
    #
    @9
    @11
    wb
    #
    @0
    @12
    wa
    @5
    chil
    wcel
    #
    @6
    chil
    wcel
    #
    @13
    @1
    @12
    wa
    chil
    chil
    @4
    cS
    ffvelrn
    chil
    chil
    @4
    cT
    ffvelrn
    @14
    @15
    wa
    @9
    @5
    @6
    wceq
    @11
    vx
    @5
    @6
    hial2eq2
    vx
    @5
    @6
    hial2eq
    bitr4d
    syl2an
    anandirs
    ralbidva
    vy
    vx
    cS
    cT
    hoeq1
    3bitrd
end
