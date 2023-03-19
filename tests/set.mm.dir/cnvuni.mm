include "cuni.mm"
include "ccnv.mm"
include "cv.mm"
include "ciun.mm"
include "wcel.mm"
include "wrex.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "elcnv2.mm"
include "eluni2.mm"
include "anbi2i.mm"
include "r19.42v.mm"
include "bitr4i.mm"
include "2exbii.mm"
include "rexbii.mm"
include "rexcom4.mm"
include "exbii.mm"
include "3bitrri.mm"
include "3bitri.mm"
include "eliun.mm"
include "eqriv.mm"

theorem cnvuni
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  assert |- `' U. A = U_ x e. A `' x

  proof
    vy
    cA
    cuni
    #
    ccnv
    #
    vx
    cA
    vx
    cv
    #
    ccnv
    #
    ciun
    #
    vy
    cv
    #
    @1
    wcel
    #
    @5
    @3
    wcel
    #
    vx
    cA
    wrex
    #
    @5
    @4
    wcel
    @6
    @5
    vz
    cv
    #
    vw
    cv
    #
    cop
    wceq
    #
    @10
    @9
    cop
    #
    @0
    wcel
    #
    wa
    #
    vw
    wex
    vz
    wex
    @11
    @12
    @2
    wcel
    #
    wa
    #
    vx
    cA
    wrex
    #
    vw
    wex
    #
    vz
    wex
    #
    @8
    vz
    vw
    @5
    @0
    elcnv2
    @14
    @17
    vz
    vw
    @14
    @11
    @15
    vx
    cA
    wrex
    #
    wa
    @17
    @13
    @20
    @11
    vx
    @12
    cA
    eluni2
    anbi2i
    @11
    @15
    vx
    cA
    r19.42v
    bitr4i
    2exbii
    @8
    @16
    vw
    wex
    #
    vz
    wex
    #
    vx
    cA
    wrex
    @21
    vx
    cA
    wrex
    #
    vz
    wex
    @19
    @7
    @22
    vx
    cA
    vz
    vw
    @5
    @2
    elcnv2
    rexbii
    @21
    vx
    vz
    cA
    rexcom4
    @23
    @18
    vz
    @16
    vx
    vw
    cA
    rexcom4
    exbii
    3bitrri
    3bitri
    vx
    @5
    cA
    @3
    eliun
    bitr4i
    eqriv
end
