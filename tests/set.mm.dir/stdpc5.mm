include "wi.mm"
include "wal.mm"
include "19.21.mm"
include "biimpi.mm"

theorem stdpc5
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume stdpc5.1: |- F/ x ph


  assert |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) )

  proof
    wph
    wps
    wi
    vx
    wal
    wph
    wps
    vx
    wal
    wi
    wph
    wps
    vx
    stdpc5.1
    19.21
    biimpi
end
