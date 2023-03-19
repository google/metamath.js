include "wal.mm"
include "wi.mm"
include "wnf.mm"
include "wex.mm"
include "wb.mm"
include "nf5.mm"
include "19.23t.mm"
include "sylbir.mm"

theorem axie2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ps -> A. x ps ) -> ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) )

  proof
    wps
    wps
    vx
    wal
    wi
    vx
    wal
    wps
    vx
    wnf
    wph
    wps
    wi
    vx
    wal
    wph
    vx
    wex
    wps
    wi
    wb
    wps
    vx
    nf5
    wph
    wps
    vx
    19.23t
    sylbir
end
