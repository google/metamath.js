include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "cxp.mm"
include "ciun.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "wceq.mm"
include "sneq.mm"
include "fveq2.mm"
include "xpeq12d.mm"
include "cbviunv.mm"
include "wrex.mm"
include "df-xp.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "iunopab.mm"
include "velsn.mm"
include "equcom.mm"
include "bitri.mm"
include "anbi1i.mm"
include "rexbii.mm"
include "eleq2d.mm"
include "ceqsrexbv.mm"
include "opabbii.mm"
include "3eqtri.mm"

theorem marypha2lem2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cT: class T
  let cF: class F
  let vz: setvar z
  let cG: class G
  let cX: class X
  assume marypha2lem.t: |- T = U_ x e. A ( { x } X. ( F ` x ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint G x
  disjoint G y
  disjoint X x
  disjoint X y
  assert |- T = { <. x , y >. | ( x e. A /\ y e. ( F ` x ) ) }

  proof
    cT
    vx
    cA
    vx
    cv
    #
    csn
    #
    @0
    cF
    cfv
    #
    cxp
    #
    ciun
    vz
    cA
    vz
    cv
    #
    csn
    #
    @4
    cF
    cfv
    #
    cxp
    #
    ciun
    #
    @0
    cA
    wcel
    vy
    cv
    #
    @2
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    marypha2lem.t
    vx
    vz
    cA
    @3
    @7
    @0
    @4
    wceq
    #
    @1
    @5
    @2
    @6
    @0
    @4
    sneq
    @0
    @4
    cF
    fveq2
    xpeq12d
    cbviunv
    @8
    vz
    cA
    @0
    @5
    wcel
    #
    @9
    @6
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    ciun
    @16
    vz
    cA
    wrex
    #
    vx
    vy
    copab
    @12
    vz
    cA
    @7
    @17
    @7
    @17
    wceq
    @4
    cA
    wcel
    vx
    vy
    @5
    @6
    df-xp
    a1i
    iuneq2i
    @16
    vx
    vy
    vz
    cA
    iunopab
    @18
    @11
    vx
    vy
    @18
    @4
    @0
    wceq
    #
    @15
    wa
    #
    vz
    cA
    wrex
    @11
    @16
    @20
    vz
    cA
    @14
    @19
    @15
    @14
    @13
    @19
    vx
    @4
    velsn
    vx
    vz
    equcom
    bitri
    anbi1i
    rexbii
    @15
    @10
    vz
    @0
    cA
    @19
    @6
    @2
    @9
    @4
    @0
    cF
    fveq2
    eleq2d
    ceqsrexbv
    bitri
    opabbii
    3eqtri
    3eqtri
end
