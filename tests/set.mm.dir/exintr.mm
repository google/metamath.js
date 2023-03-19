include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wa.mm"
include "exintrbi.mm"
include "biimpd.mm"

theorem exintr
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ( ph /\ ps ) ) )

  proof
    wph
    wps
    wi
    vx
    wal
    wph
    vx
    wex
    wph
    wps
    wa
    vx
    wex
    wph
    wps
    vx
    exintrbi
    biimpd
end
