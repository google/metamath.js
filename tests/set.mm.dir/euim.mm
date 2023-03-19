include "wex.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "weu.mm"
include "wmo.mm"
include "ax-1.mm"
include "euimmo.mm"
include "anim12ii.mm"
include "eu5.mm"
include "syl6ibr.mm"

theorem euim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( E. x ph /\ A. x ( ph -> ps ) ) -> ( E! x ps -> E! x ph ) )

  proof
    wph
    vx
    wex
    #
    wph
    wps
    wi
    vx
    wal
    #
    wa
    wps
    vx
    weu
    #
    @0
    wph
    vx
    wmo
    #
    wa
    wph
    vx
    weu
    @0
    @2
    @0
    @1
    @3
    @0
    @2
    ax-1
    wph
    wps
    vx
    euimmo
    anim12ii
    wph
    vx
    eu5
    syl6ibr
end
