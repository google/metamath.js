include "wi.mm"
include "wal.mm"
include "alim.mm"
include "al2im.mm"
include "syl6.mm"

theorem al3im
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x


  assert |- ( A. x ( ph -> ( ps -> ( ch -> th ) ) ) -> ( A. x ph -> ( A. x ps -> ( A. x ch -> A. x th ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wi
    wi
    #
    wi
    vx
    wal
    wph
    vx
    wal
    @0
    vx
    wal
    wps
    vx
    wal
    wch
    vx
    wal
    wth
    vx
    wal
    wi
    wi
    wph
    @0
    vx
    alim
    wps
    wch
    wth
    vx
    al2im
    syl6
end
