include "wnfOLD.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wb.mm"
include "19.23tOLD.mm"
include "ax-mp.mm"

theorem 19.23OLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.23OLD.1: |- nfOLD x ps


  assert |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) )

  proof
    wps
    vx
    wnfOLD
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
    19.23OLD.1
    wph
    wps
    vx
    19.23tOLD
    ax-mp
end
