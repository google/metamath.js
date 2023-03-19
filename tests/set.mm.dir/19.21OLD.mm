include "wnfOLD.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "19.21tOLD.mm"
include "ax-mp.mm"

theorem 19.21OLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.21OLD.1: |- nfOLD x ph


  assert |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) )

  proof
    wph
    vx
    wnfOLD
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
    19.21OLD.1
    wph
    wps
    vx
    19.21tOLD
    ax-mp
end
