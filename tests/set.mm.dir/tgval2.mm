include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "cv.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "wss.mm"
include "cab.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "tgval.mm"
include "inss1.mm"
include "unissi.mm"
include "sseli.mm"
include "pm4.71ri.mm"
include "ralbii.mm"
include "r19.26.mm"
include "bitri.mm"
include "dfss3.mm"
include "wex.mm"
include "elin.mm"
include "anbi2i.mm"
include "an12.mm"
include "exbii.mm"
include "eluni.mm"
include "df-rex.mm"
include "3bitr4i.mm"
include "selpw.mm"
include "rexbii.mm"
include "bitr2i.mm"
include "anbi12i.mm"
include "abbii.mm"
include "syl6eq.mm"

theorem tgval2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cV: class V
  let cA: class A
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J
  let cC: class C

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint C x
  disjoint C y
  assert |- ( B e. V -> ( topGen ` B ) = { x | ( x C_ U. B /\ A. y e. x E. z e. B ( y e. z /\ z C_ x ) ) } )

  proof
    cB
    cV
    wcel
    cB
    ctg
    cfv
    vx
    cv
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
    vx
    cab
    @0
    cB
    cuni
    #
    wss
    #
    vy
    cv
    #
    vz
    cv
    #
    wcel
    #
    @8
    @0
    wss
    #
    wa
    #
    vz
    cB
    wrex
    #
    vy
    @0
    wral
    #
    wa
    #
    vx
    cab
    vx
    cB
    cV
    tgval
    @4
    @14
    vx
    @7
    @3
    wcel
    #
    vy
    @0
    wral
    #
    @7
    @5
    wcel
    #
    vy
    @0
    wral
    #
    @16
    wa
    #
    @4
    @14
    @16
    @17
    @15
    wa
    #
    vy
    @0
    wral
    @19
    @15
    @20
    vy
    @0
    @15
    @17
    @3
    @5
    @7
    @2
    cB
    cB
    @1
    inss1
    unissi
    sseli
    pm4.71ri
    ralbii
    @17
    @15
    vy
    @0
    r19.26
    bitri
    vy
    @0
    @3
    dfss3
    @6
    @18
    @13
    @16
    vy
    @0
    @5
    dfss3
    @12
    @15
    vy
    @0
    @15
    @9
    @8
    @1
    wcel
    #
    wa
    #
    vz
    cB
    wrex
    #
    @12
    @9
    @8
    @2
    wcel
    #
    wa
    #
    vz
    wex
    @8
    cB
    wcel
    #
    @22
    wa
    #
    vz
    wex
    @15
    @23
    @25
    @27
    vz
    @25
    @9
    @26
    @21
    wa
    #
    wa
    @27
    @24
    @28
    @9
    @8
    cB
    @1
    elin
    anbi2i
    @9
    @26
    @21
    an12
    bitri
    exbii
    vz
    @7
    @2
    eluni
    @22
    vz
    cB
    df-rex
    3bitr4i
    @22
    @11
    vz
    cB
    @21
    @10
    @9
    vz
    @0
    selpw
    anbi2i
    rexbii
    bitr2i
    ralbii
    anbi12i
    3bitr4i
    abbii
    syl6eq
end
