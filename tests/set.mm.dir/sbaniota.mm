include "weu.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "cio.mm"
include "wsbc.mm"
include "eupickbi.mm"
include "sbiota1.mm"
include "bitrd.mm"

theorem sbaniota
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E! x ph -> ( E. x ( ph /\ ps ) <-> [. ( iota x ph ) / x ]. ps ) )

  proof
    wph
    vx
    weu
    wph
    wps
    wa
    vx
    wex
    wph
    wps
    wi
    vx
    wal
    wps
    vx
    wph
    vx
    cio
    wsbc
    wph
    wps
    vx
    eupickbi
    wph
    wps
    vx
    sbiota1
    bitrd
end
