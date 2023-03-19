include "ccoss.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wrel.mm"
include "wb.mm"
include "relcoss.mm"
include "ssrel3.mm"
include "ax-mp.mm"
include "wex.mm"
include "cvv.mm"
include "brcoss.mm"
include "el2v.mm"
include "brcosscnvcoss.mm"
include "anbi1i.mm"
include "exbii.mm"
include "bitri.mm"
include "imbi1i.mm"
include "19.23v.mm"
include "bitr4i.mm"
include "albii.mm"
include "alcom.mm"

theorem cocossss
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cS: class S

  disjoint R x
  disjoint R y
  disjoint R z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint S x
  disjoint S y
  disjoint S z
  assert |- ( ,~ ,~ R C_ S <-> A. x A. y A. z ( ( x ,~ R y /\ y ,~ R z ) -> x S z ) )

  proof
    cR
    ccoss
    #
    ccoss
    #
    cS
    wss
    #
    vx
    cv
    #
    vz
    cv
    #
    @1
    wbr
    #
    @3
    @4
    cS
    wbr
    #
    wi
    #
    vz
    wal
    #
    vx
    wal
    #
    @3
    vy
    cv
    #
    @0
    wbr
    #
    @10
    @4
    @0
    wbr
    #
    wa
    #
    @6
    wi
    #
    vz
    wal
    vy
    wal
    #
    vx
    wal
    @1
    wrel
    @2
    @9
    wb
    @0
    relcoss
    vx
    vz
    @1
    cS
    ssrel3
    ax-mp
    @8
    @15
    vx
    @8
    @14
    vy
    wal
    #
    vz
    wal
    @15
    @7
    @16
    vz
    @7
    @13
    vy
    wex
    #
    @6
    wi
    @16
    @5
    @17
    @6
    @5
    @10
    @3
    @0
    wbr
    #
    @12
    wa
    #
    vy
    wex
    #
    @17
    @5
    @20
    wb
    vx
    vz
    vy
    @3
    @4
    @0
    cvv
    cvv
    brcoss
    el2v
    @19
    @13
    vy
    @18
    @11
    @12
    @18
    @11
    wb
    vy
    vx
    @10
    @3
    cR
    cvv
    cvv
    brcosscnvcoss
    el2v
    anbi1i
    exbii
    bitri
    imbi1i
    @13
    @6
    vy
    19.23v
    bitr4i
    albii
    @14
    vz
    vy
    alcom
    bitri
    albii
    bitri
end
