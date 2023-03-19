include "wi.mm"
include "wal.mm"
include "alim.mm"
include "syl6.mm"

theorem al2im
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( A. x ( ph -> ( ps -> ch ) ) -> ( A. x ph -> ( A. x ps -> A. x ch ) ) )

  proof
    wph
    wps
    wch
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
    wi
    wph
    @0
    vx
    alim
    wps
    wch
    vx
    alim
    syl6
end
