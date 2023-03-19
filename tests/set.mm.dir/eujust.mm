include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "equequ2.mm"
include "bibi2d.mm"
include "albidv.mm"
include "cbvexv.mm"
include "bitri.mm"

theorem eujust
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint ph y
  disjoint ph z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  assert |- ( E. y A. x ( ph <-> x = y ) <-> E. z A. x ( ph <-> x = z ) )

  proof
    wph
    vx
    vy
    weq
    #
    wb
    #
    vx
    wal
    #
    vy
    wex
    wph
    vx
    vw
    weq
    #
    wb
    #
    vx
    wal
    #
    vw
    wex
    wph
    vx
    vz
    weq
    #
    wb
    #
    vx
    wal
    #
    vz
    wex
    @2
    @5
    vy
    vw
    vy
    vw
    weq
    #
    @1
    @4
    vx
    @9
    @0
    @3
    wph
    vy
    vw
    vx
    equequ2
    bibi2d
    albidv
    cbvexv
    @5
    @8
    vw
    vz
    vw
    vz
    weq
    #
    @4
    @7
    vx
    @10
    @3
    @6
    wph
    vw
    vz
    vx
    equequ2
    bibi2d
    albidv
    cbvexv
    bitri
end
