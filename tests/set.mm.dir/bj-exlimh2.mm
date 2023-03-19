include "wi.mm"
include "wal.mm"
include "wex.mm"
include "bj-exlimh.mm"
include "imp.mm"

theorem bj-exlimh2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( ( A. x ( ph -> ps ) /\ ( E. x ps -> ch ) ) -> ( E. x ph -> ch ) )

  proof
    wph
    wps
    wi
    vx
    wal
    wps
    vx
    wex
    wch
    wi
    wph
    vx
    wex
    wch
    wi
    wph
    wps
    wch
    vx
    bj-exlimh
    imp
end
