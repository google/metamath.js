include "wnf.mm"
include "wal.mm"
include "wi.mm"
include "wn.mm"
include "wex.mm"
include "nf5r.mm"
include "bj-nexdh.mm"
include "syl5com.mm"

theorem bj-nexdt
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( F/ x ph -> ( A. x ( ph -> -. ps ) -> ( ph -> -. E. x ps ) ) )

  proof
    wph
    vx
    wnf
    wph
    wph
    vx
    wal
    wi
    wph
    wps
    wn
    wi
    vx
    wal
    wph
    wps
    vx
    wex
    wn
    wi
    wph
    vx
    nf5r
    wph
    wps
    wph
    vx
    bj-nexdh
    syl5com
end
