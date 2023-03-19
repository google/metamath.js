include "wel.mm"
include "wa.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "weq.mm"
include "elequ2.mm"
include "anbi1d.mm"
include "anabs5.mm"
include "syl6bb.mm"
include "bibi2d.mm"
include "albidv.mm"
include "exbidv.mm"
include "ax-sep.mm"
include "chvarv.mm"

theorem axsep2
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
    vx
    vz
    wel
    #
    wph
    wa
    #
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
    @3
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
    @6
    @8
    vy
    @9
    @5
    @7
    vx
    @9
    @4
    @3
    @0
    @9
    @4
    @2
    @3
    wa
    @3
    @9
    @1
    @2
    @3
    vw
    vz
    vx
    elequ2
    anbi1d
    @2
    wph
    anabs5
    syl6bb
    bibi2d
    albidv
    exbidv
    @3
    vx
    vy
    vw
    ax-sep
    chvarv
end
