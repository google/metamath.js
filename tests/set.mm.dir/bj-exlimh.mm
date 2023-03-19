include "wi.mm"
include "wal.mm"
include "wex.mm"
include "exim.mm"
include "imim1d.mm"

theorem bj-exlimh
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( A. x ( ph -> ps ) -> ( ( E. x ps -> ch ) -> ( E. x ph -> ch ) ) )

  proof
    wph
    wps
    wi
    vx
    wal
    wph
    vx
    wex
    wps
    vx
    wex
    wch
    wph
    wps
    vx
    exim
    imim1d
end
