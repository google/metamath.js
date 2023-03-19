include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cxp.mm"
include "xpex.mm"
include "wmo.mm"
include "wcel.mm"
include "moeq.mm"
include "mosubop.mm"
include "anass.mm"
include "2exbii.mm"
include "19.42vv.mm"
include "bitri.mm"
include "mobii.mm"
include "mpbir.mm"
include "a1i.mm"
include "oprabex.mm"

theorem oprabex3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cR: class R
  let vf: setvar f
  let cF: class F
  let cH: class H
  assume oprabex3.1: |- H e. _V
  assume oprabex3.2: |- F = { <. <. x , y >. , z >. | ( ( x e. ( H X. H ) /\ y e. ( H X. H ) ) /\ E. w E. v E. u E. f ( ( x = <. w , v >. /\ y = <. u , f >. ) /\ z = R ) ) }

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint f x
  disjoint H x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint f y
  disjoint H y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint f z
  disjoint H z
  disjoint v w
  disjoint u w
  disjoint f w
  disjoint H w
  disjoint u v
  disjoint f v
  disjoint H v
  disjoint f u
  disjoint H u
  disjoint H f
  disjoint R x
  disjoint R y
  disjoint R z
  assert |- F e. _V

  proof
    vx
    cv
    #
    vw
    cv
    vv
    cv
    cop
    wceq
    #
    vy
    cv
    #
    vu
    cv
    vf
    cv
    cop
    wceq
    #
    wa
    vz
    cv
    cR
    wceq
    #
    wa
    #
    vf
    wex
    vu
    wex
    #
    vv
    wex
    vw
    wex
    #
    vx
    vy
    vz
    cH
    cH
    cxp
    #
    @8
    cF
    cH
    cH
    oprabex3.1
    oprabex3.1
    xpex
    #
    @9
    @7
    vz
    wmo
    #
    @0
    @8
    wcel
    @2
    @8
    wcel
    wa
    @10
    @1
    @3
    @4
    wa
    #
    vf
    wex
    vu
    wex
    #
    wa
    #
    vv
    wex
    vw
    wex
    #
    vz
    wmo
    @12
    vz
    vw
    vv
    @0
    @4
    vz
    vu
    vf
    @2
    vz
    cR
    moeq
    mosubop
    mosubop
    @7
    @14
    vz
    @6
    @13
    vw
    vv
    @6
    @1
    @11
    wa
    #
    vf
    wex
    vu
    wex
    @13
    @5
    @15
    vu
    vf
    @1
    @3
    @4
    anass
    2exbii
    @1
    @11
    vu
    vf
    19.42vv
    bitri
    2exbii
    mobii
    mpbir
    a1i
    oprabex3.2
    oprabex
end
