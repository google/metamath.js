include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "bj-nexdh.mm"
include "imp.mm"

theorem bj-nexdh2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( ( A. x ( ph -> -. ps ) /\ ( ch -> A. x ph ) ) -> ( ch -> -. E. x ps ) )

  proof
    wph
    wps
    wn
    wi
    vx
    wal
    wch
    wph
    vx
    wal
    wi
    wch
    wps
    vx
    wex
    wn
    wi
    wph
    wps
    wch
    vx
    bj-nexdh
    imp
end
