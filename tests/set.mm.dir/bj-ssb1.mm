include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wssb.mm"
include "19.21v.mm"
include "albii.mm"
include "wex.mm"
include "19.23v.mm"
include "equequ2.mm"
include "imbi1d.mm"
include "pm5.74i.mm"
include "ax6ev.mm"
include "a1bi.mm"
include "3bitr4ri.mm"
include "alcom.mm"
include "bitri.mm"
include "df-ssb.mm"

theorem bj-ssb1
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let vy: setvar y

  disjoint t x
  disjoint x y
  disjoint t y
  disjoint ph y
  assert |- ( [b t /b x ]b ph <-> A. x ( x = t -> ph ) )

  proof
    vy
    vt
    weq
    #
    vx
    vy
    weq
    #
    wph
    wi
    #
    wi
    #
    vx
    wal
    #
    vy
    wal
    #
    @0
    @2
    vx
    wal
    wi
    #
    vy
    wal
    vx
    vt
    weq
    #
    wph
    wi
    #
    vx
    wal
    #
    wph
    vx
    vt
    wssb
    @4
    @6
    vy
    @0
    @2
    vx
    19.21v
    albii
    @9
    @3
    vy
    wal
    #
    vx
    wal
    @5
    @8
    @10
    vx
    @0
    @8
    wi
    #
    vy
    wal
    @0
    vy
    wex
    #
    @8
    wi
    @10
    @8
    @0
    @8
    vy
    19.23v
    @3
    @11
    vy
    @0
    @2
    @8
    @0
    @1
    @7
    wph
    vy
    vt
    vx
    equequ2
    imbi1d
    pm5.74i
    albii
    @12
    @8
    vy
    vt
    ax6ev
    a1bi
    3bitr4ri
    albii
    @3
    vx
    vy
    alcom
    bitri
    wph
    vx
    vy
    vt
    df-ssb
    3bitr4ri
end
