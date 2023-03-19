include "wcel.mm"
include "ctb.mm"
include "cv.mm"
include "cin.mm"
include "cpw.mm"
include "cuni.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "isbasisg.mm"
include "dfss3.mm"
include "wex.mm"
include "elin.mm"
include "selpw.mm"
include "anbi2i.mm"
include "bitri.mm"
include "an12.mm"
include "exbii.mm"
include "eluni.mm"
include "df-rex.mm"
include "3bitr4i.mm"
include "ralbii.mm"
include "2ralbii.mm"
include "syl6bb.mm"

theorem isbasis2g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cC: class C

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  assert |- ( B e. C -> ( B e. TopBases <-> A. x e. B A. y e. B A. z e. ( x i^i y ) E. w e. B ( z e. w /\ w C_ ( x i^i y ) ) ) )

  proof
    cB
    cC
    wcel
    cB
    ctb
    wcel
    vx
    cv
    vy
    cv
    cin
    #
    cB
    @0
    cpw
    #
    cin
    #
    cuni
    #
    wss
    #
    vy
    cB
    wral
    vx
    cB
    wral
    vz
    cv
    #
    vw
    cv
    #
    wcel
    #
    @6
    @0
    wss
    #
    wa
    #
    vw
    cB
    wrex
    #
    vz
    @0
    wral
    #
    vy
    cB
    wral
    vx
    cB
    wral
    vx
    vy
    cB
    cC
    isbasisg
    @4
    @11
    vx
    vy
    cB
    cB
    @4
    @5
    @3
    wcel
    #
    vz
    @0
    wral
    @11
    vz
    @0
    @3
    dfss3
    @12
    @10
    vz
    @0
    @7
    @6
    @2
    wcel
    #
    wa
    #
    vw
    wex
    @6
    cB
    wcel
    #
    @9
    wa
    #
    vw
    wex
    @12
    @10
    @14
    @16
    vw
    @14
    @7
    @15
    @8
    wa
    #
    wa
    @16
    @13
    @17
    @7
    @13
    @15
    @6
    @1
    wcel
    #
    wa
    @17
    @6
    cB
    @1
    elin
    @18
    @8
    @15
    vw
    @0
    selpw
    anbi2i
    bitri
    anbi2i
    @7
    @15
    @8
    an12
    bitri
    exbii
    vw
    @5
    @2
    eluni
    @9
    vw
    cB
    df-rex
    3bitr4i
    ralbii
    bitri
    2ralbii
    syl6bb
end
