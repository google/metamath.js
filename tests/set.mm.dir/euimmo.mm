include "weu.mm"
include "wmo.mm"
include "wi.mm"
include "wal.mm"
include "eumo.mm"
include "moim.mm"
include "syl5.mm"

theorem euimmo
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph -> ps ) -> ( E! x ps -> E* x ph ) )

  proof
    wps
    vx
    weu
    wps
    vx
    wmo
    wph
    wps
    wi
    vx
    wal
    wph
    vx
    wmo
    wps
    vx
    eumo
    wph
    wps
    vx
    moim
    syl5
end
