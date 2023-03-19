include "weu.mm"
include "wex.mm"
include "wmo.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "eu5.mm"
include "mo4.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem eu4
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume eu4.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint ph y
  disjoint ps x
  assert |- ( E! x ph <-> ( E. x ph /\ A. x A. y ( ( ph /\ ps ) -> x = y ) ) )

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
    wps
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
    wps
    vx
    vy
    eu4.1
    mo4
    anbi2i
    bitri
end
