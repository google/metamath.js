include "cuni.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "df-rex.mm"
include "rexbii.mm"
include "rexcom4.mm"
include "bitri.mm"
include "r19.41v.mm"
include "exbii.mm"
include "eluni2.mm"
include "eliun.mm"
include "anbi1i.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem iuncom4
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z


  assert |- U_ x e. A U. B = U. U_ x e. A B

  proof
    vy
    vx
    cA
    cB
    cuni
    #
    ciun
    #
    vx
    cA
    cB
    ciun
    #
    cuni
    #
    vy
    cv
    #
    @0
    wcel
    #
    vx
    cA
    wrex
    #
    @4
    vz
    cv
    #
    wcel
    #
    vz
    @2
    wrex
    #
    @4
    @1
    wcel
    @4
    @3
    wcel
    @8
    vz
    cB
    wrex
    #
    vx
    cA
    wrex
    #
    @7
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    @8
    wa
    #
    vz
    wex
    #
    @6
    @9
    @11
    @12
    @8
    wa
    #
    vx
    cA
    wrex
    #
    vz
    wex
    #
    @15
    @11
    @16
    vz
    wex
    #
    vx
    cA
    wrex
    @18
    @10
    @19
    vx
    cA
    @8
    vz
    cB
    df-rex
    rexbii
    @16
    vx
    vz
    cA
    rexcom4
    bitri
    @17
    @14
    vz
    @12
    @8
    vx
    cA
    r19.41v
    exbii
    bitri
    @5
    @10
    vx
    cA
    vz
    @4
    cB
    eluni2
    rexbii
    @9
    @7
    @2
    wcel
    #
    @8
    wa
    #
    vz
    wex
    @15
    @8
    vz
    @2
    df-rex
    @21
    @14
    vz
    @20
    @13
    @8
    vx
    @7
    cA
    cB
    eliun
    anbi1i
    exbii
    bitri
    3bitr4i
    vx
    @4
    cA
    @0
    eliun
    vz
    @4
    @2
    eluni2
    3bitr4i
    eqriv
end
