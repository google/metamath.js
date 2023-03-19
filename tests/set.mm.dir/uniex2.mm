include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "wex.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "wa.mm"
include "zfun.mm"
include "eluni.mm"
include "imbi1i.mm"
include "albii.mm"
include "exbii.mm"
include "mpbir.mm"
include "bm1.3ii.mm"
include "dfcleq.mm"

theorem uniex2
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  assert |- E. y y = U. x

  proof
    vy
    cv
    #
    vx
    cv
    #
    cuni
    #
    wceq
    #
    vy
    wex
    vz
    cv
    #
    @0
    wcel
    #
    @4
    @2
    wcel
    #
    wb
    vz
    wal
    #
    vy
    wex
    @6
    vy
    vz
    @6
    @5
    wi
    #
    vz
    wal
    #
    vy
    wex
    @5
    @0
    @1
    wcel
    wa
    vy
    wex
    #
    @5
    wi
    #
    vz
    wal
    #
    vy
    wex
    vy
    vz
    vx
    zfun
    @9
    @12
    vy
    @8
    @11
    vz
    @6
    @10
    @5
    vy
    @4
    @1
    eluni
    imbi1i
    albii
    exbii
    mpbir
    bm1.3ii
    @3
    @7
    vy
    vz
    @0
    @2
    dfcleq
    exbii
    mpbir
end
