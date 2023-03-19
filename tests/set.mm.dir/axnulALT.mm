include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wal.mm"
include "wex.mm"
include "wfal.mm"
include "wa.mm"
include "wb.mm"
include "wceq.mm"
include "wi.mm"
include "ax-rep.mm"
include "sp.mm"
include "con2i.mm"
include "df-ex.mm"
include "sylibr.mm"
include "fal.mm"
include "mto.mm"
include "pm2.21i.mm"
include "mpg.mm"
include "intnan.mm"
include "nex.mm"
include "nbn.mm"
include "albii.mm"
include "exbii.mm"
include "mpbir.mm"

theorem axnulALT
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  assert |- E. x A. y -. y e. x

  proof
    vy
    cv
    #
    vx
    cv
    #
    wcel
    #
    wn
    #
    vy
    wal
    #
    vx
    wex
    @2
    vw
    cv
    vz
    cv
    wcel
    #
    wfal
    vx
    wal
    #
    wa
    #
    vw
    wex
    #
    wb
    #
    vy
    wal
    #
    vx
    wex
    #
    @6
    @0
    @1
    wceq
    #
    wi
    #
    vy
    wal
    #
    vx
    wex
    #
    @11
    vw
    wfal
    vz
    vx
    vy
    vw
    ax-rep
    @13
    @15
    vy
    @14
    @14
    wn
    #
    vx
    wal
    #
    wn
    @15
    @17
    @14
    @16
    vx
    sp
    con2i
    @14
    vx
    df-ex
    sylibr
    @6
    @12
    @6
    wfal
    fal
    wfal
    vx
    sp
    mto
    #
    pm2.21i
    mpg
    mpg
    @4
    @10
    vx
    @3
    @9
    vy
    @8
    @2
    @7
    vw
    @6
    @5
    @18
    intnan
    nex
    nbn
    albii
    exbii
    mpbir
end
