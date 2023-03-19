include "weu.mm"
include "wex.mm"
include "wmo.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "eu5.mm"
include "mo2.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem bj-eu3f
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume bj-eu3f.1: |- F/ y ph

  disjoint x y
  assert |- ( E! x ph <-> ( E. x ph /\ E. y A. x ( ph -> x = y ) ) )

  proof
    wph
    vx
    weu
    wph
    vx
    wex
    #
    wph
    vx
    wmo
    #
    wa
    @0
    wph
    vx
    vy
    weq
    wi
    vx
    wal
    vy
    wex
    #
    wa
    wph
    vx
    eu5
    @1
    @2
    @0
    wph
    vx
    vy
    bj-eu3f.1
    mo2
    anbi2i
    bitri
end
