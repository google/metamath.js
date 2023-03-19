include "wnf.mm"
include "wi.mm"
include "wal.mm"
include "bj-alrim.mm"
include "imp.mm"

theorem bj-alrim2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( F/ x ph /\ A. x ( ph -> ps ) ) -> ( ph -> A. x ps ) )

  proof
    wph
    vx
    wnf
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
    bj-alrim
    imp
end
