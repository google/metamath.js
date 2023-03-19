include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "alinexa.mm"
include "con2bii.mm"

theorem bj-exnalimn
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E. x ( ph /\ ps ) <-> -. A. x ( ph -> -. ps ) )

  proof
    wph
    wps
    wn
    wi
    vx
    wal
    wph
    wps
    wa
    vx
    wex
    wph
    wps
    vx
    alinexa
    con2bii
end
