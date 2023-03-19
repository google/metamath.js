include "wel.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wb.mm"
include "wex.mm"
include "19.42v.mm"
include "bimsc1.mm"
include "alanimi.mm"
include "eximi.mm"
include "sylbir.mm"
include "weq.mm"
include "elequ2.mm"
include "imbi2d.mm"
include "albidv.mm"
include "cbvexv.mm"
include "mpbi.mm"
include "ax-sep.mm"
include "pm3.2i.mm"
include "exan.mm"
include "exlimiiv.mm"

theorem bm1.3ii
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume bm1.3ii.1: |- E. x A. y ( ph -> y e. x )

  disjoint ph x
  disjoint x y
  disjoint x z
  disjoint ph z
  disjoint y z
  assert |- E. x A. y ( y e. x <-> ph )

  proof
    wph
    vy
    vz
    wel
    #
    wi
    #
    vy
    wal
    #
    vy
    vx
    wel
    #
    @0
    wph
    wa
    wb
    #
    vy
    wal
    #
    vx
    wex
    #
    wa
    #
    @3
    wph
    wb
    #
    vy
    wal
    #
    vx
    wex
    #
    vz
    @7
    @2
    @5
    wa
    #
    vx
    wex
    @10
    @2
    @5
    vx
    19.42v
    @11
    @9
    vx
    @1
    @4
    @8
    vy
    wph
    @0
    @3
    bimsc1
    alanimi
    eximi
    sylbir
    @2
    @6
    vz
    @2
    vz
    wex
    #
    @6
    wph
    @3
    wi
    #
    vy
    wal
    #
    vx
    wex
    @12
    bm1.3ii.1
    @14
    @2
    vx
    vz
    vx
    vz
    weq
    #
    @13
    @1
    vy
    @15
    @3
    @0
    wph
    vx
    vz
    vy
    elequ2
    imbi2d
    albidv
    cbvexv
    mpbi
    wph
    vy
    vx
    vz
    ax-sep
    pm3.2i
    exan
    exlimiiv
end
