include "wel.mm"
include "wa.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "weq.mm"
include "elequ2.mm"
include "anbi1d.mm"
include "bibi2d.mm"
include "albidv.mm"
include "exbidv.mm"
include "ax-sep.mm"
include "bj-chvarvv.mm"

theorem bj-axsep2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  assert |- E. y A. x ( x e. y <-> ( x e. z /\ ph ) )

  proof
    vx
    vy
    wel
    #
    vx
    vw
    wel
    #
    wph
    wa
    #
    wb
    #
    vx
    wal
    #
    vy
    wex
    @0
    vx
    vz
    wel
    #
    wph
    wa
    #
    wb
    #
    vx
    wal
    #
    vy
    wex
    vw
    vz
    vw
    vz
    weq
    #
    @4
    @8
    vy
    @9
    @3
    @7
    vx
    @9
    @2
    @6
    @0
    @9
    @1
    @5
    wph
    vw
    vz
    vx
    elequ2
    anbi1d
    bibi2d
    albidv
    exbidv
    wph
    vx
    vy
    vw
    ax-sep
    bj-chvarvv
end
