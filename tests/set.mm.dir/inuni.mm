include "cuni.mm"
include "cin.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "eluni2.mm"
include "anbi1i.mm"
include "elin.mm"
include "ancom.mm"
include "r19.41v.mm"
include "bitr4i.mm"
include "exbii.mm"
include "rexcom4.mm"
include "vex.mm"
include "inex1.mm"
include "eleq2.mm"
include "ceqsexv.mm"
include "bitri.mm"
include "rexbii.mm"
include "3bitr4i.mm"
include "eluniab.mm"
include "eqriv.mm"

theorem inuni
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint B z
  assert |- ( U. A i^i B ) = U. { x | E. y e. A x = ( y i^i B ) }

  proof
    vz
    cA
    cuni
    #
    cB
    cin
    #
    vx
    cv
    #
    vy
    cv
    #
    cB
    cin
    #
    wceq
    #
    vy
    cA
    wrex
    #
    vx
    cab
    cuni
    #
    vz
    cv
    #
    @1
    wcel
    #
    @8
    @2
    wcel
    #
    @6
    wa
    #
    vx
    wex
    #
    @8
    @7
    wcel
    @8
    @0
    wcel
    #
    @8
    cB
    wcel
    #
    wa
    @8
    @3
    wcel
    #
    vy
    cA
    wrex
    #
    @14
    wa
    #
    @9
    @12
    @13
    @16
    @14
    vy
    @8
    cA
    eluni2
    anbi1i
    @8
    @0
    cB
    elin
    @12
    @5
    @10
    wa
    #
    vx
    wex
    #
    vy
    cA
    wrex
    #
    @17
    @12
    @18
    vy
    cA
    wrex
    #
    vx
    wex
    @20
    @11
    @21
    vx
    @11
    @6
    @10
    wa
    @21
    @10
    @6
    ancom
    @5
    @10
    vy
    cA
    r19.41v
    bitr4i
    exbii
    @18
    vy
    vx
    cA
    rexcom4
    bitr4i
    @20
    @15
    @14
    wa
    #
    vy
    cA
    wrex
    @17
    @19
    @22
    vy
    cA
    @19
    @8
    @4
    wcel
    #
    @22
    @10
    @23
    vx
    @4
    @3
    cB
    vy
    vex
    inex1
    @2
    @4
    @8
    eleq2
    ceqsexv
    @8
    @3
    cB
    elin
    bitri
    rexbii
    @15
    @14
    vy
    cA
    r19.41v
    bitri
    bitri
    3bitr4i
    @6
    vx
    @8
    eluniab
    bitr4i
    eqriv
end
