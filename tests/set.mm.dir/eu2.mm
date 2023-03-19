include "weu.mm"
include "wex.mm"
include "wmo.mm"
include "wa.mm"
include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "eu5.mm"
include "mo3.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem eu2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume eu2.1: |- F/ y ph

  disjoint x y
  assert |- ( E! x ph <-> ( E. x ph /\ A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) )

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
    wph
    vx
    vy
    wsb
    wa
    vx
    vy
    weq
    wi
    vy
    wal
    vx
    wal
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
    eu2.1
    mo3
    anbi2i
    bitri
end
