include "wal.mm"
include "wi.mm"
include "a1i.mm"
include "hbim1OLD.mm"

theorem hbimOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume hbimOLD.1: |- ( ph -> A. x ph )
  assume hbimOLD.2: |- ( ps -> A. x ps )


  assert |- ( ( ph -> ps ) -> A. x ( ph -> ps ) )

  proof
    wph
    wps
    vx
    hbimOLD.1
    wps
    wps
    vx
    wal
    wi
    wph
    hbimOLD.2
    a1i
    hbim1OLD
end
