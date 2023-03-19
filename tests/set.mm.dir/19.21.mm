include "wnf.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "19.21t.mm"
include "ax-mp.mm"

theorem 19.21
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.21.1: |- F/ x ph


  assert |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) )

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
    wb
    19.21.1
    wph
    wps
    vx
    19.21t
    ax-mp
end
