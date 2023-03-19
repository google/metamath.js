include "wel.mm"
include "cv.mm"
include "cpw.mm"
include "wss.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "cen.mm"
include "wbr.mm"
include "wo.mm"
include "w3a.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "ax-groth.mm"
include "biid.mm"
include "pwss.mm"
include "rexbii.mm"
include "anbi12i.mm"
include "ralbii.mm"
include "wcel.mm"
include "df-ral.mm"
include "selpw.mm"
include "imbi1i.mm"
include "albii.mm"
include "bitri.mm"
include "3anbi123i.mm"
include "exbii.mm"
include "mpbir.mm"

theorem axgroth5
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint v x
  disjoint u x
  disjoint v y
  disjoint u y
  disjoint v z
  disjoint u z
  disjoint v w
  disjoint u w
  disjoint u v
  assert |- E. y ( x e. y /\ A. z e. y ( ~P z C_ y /\ E. w e. y ~P z C_ w ) /\ A. z e. ~P y ( z ~~ y \/ z e. y ) )

  proof
    vx
    vy
    wel
    #
    vz
    cv
    #
    cpw
    #
    vy
    cv
    #
    wss
    #
    @2
    vw
    cv
    #
    wss
    #
    vw
    @3
    wrex
    #
    wa
    #
    vz
    @3
    wral
    #
    @1
    @3
    cen
    wbr
    vz
    vy
    wel
    wo
    #
    vz
    @3
    cpw
    #
    wral
    #
    w3a
    #
    vy
    wex
    @0
    @5
    @1
    wss
    vw
    vy
    wel
    wi
    vw
    wal
    #
    vv
    cv
    @1
    wss
    vv
    vw
    wel
    wi
    vv
    wal
    #
    vw
    @3
    wrex
    #
    wa
    #
    vz
    @3
    wral
    #
    @1
    @3
    wss
    #
    @10
    wi
    #
    vz
    wal
    #
    w3a
    #
    vy
    wex
    vx
    vy
    vz
    vw
    vv
    ax-groth
    @13
    @22
    vy
    @0
    @0
    @9
    @18
    @12
    @21
    @0
    biid
    @8
    @17
    vz
    @3
    @4
    @14
    @7
    @16
    vw
    @1
    @3
    pwss
    @6
    @15
    vw
    @3
    vv
    @1
    @5
    pwss
    rexbii
    anbi12i
    ralbii
    @12
    @1
    @11
    wcel
    #
    @10
    wi
    #
    vz
    wal
    @21
    @10
    vz
    @11
    df-ral
    @24
    @20
    vz
    @23
    @19
    @10
    vz
    @3
    selpw
    imbi1i
    albii
    bitri
    3anbi123i
    exbii
    mpbir
end
