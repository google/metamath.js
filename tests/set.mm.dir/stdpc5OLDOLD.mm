include "wnfOLD.mm"
include "wi.mm"
include "wal.mm"
include "19.21t-1OLD.mm"
include "ax-mp.mm"

theorem stdpc5OLDOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume stdpc5OLDOLD.1: |- nfOLD x ph


  assert |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) )

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
    wi
    stdpc5OLDOLD.1
    wph
    wps
    vx
    19.21t-1OLD
    ax-mp
end
