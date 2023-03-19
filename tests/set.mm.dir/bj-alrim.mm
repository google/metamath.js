include "wnf.mm"
include "wal.mm"
include "wi.mm"
include "nf5r.mm"
include "sylgt.mm"
include "syl5com.mm"

theorem bj-alrim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( F/ x ph -> ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) )

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
    wi
    vx
    wal
    wph
    wps
    vx
    wal
    wi
    wph
    vx
    nf5r
    wph
    wph
    wps
    vx
    sylgt
    syl5com
end
