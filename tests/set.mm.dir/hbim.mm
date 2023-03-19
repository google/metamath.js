include "wal.mm"
include "wi.mm"
include "a1i.mm"
include "hbim1.mm"

theorem hbim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume hbim.1: |- ( ph -> A. x ph )
  assume hbim.2: |- ( ps -> A. x ps )


  assert |- ( ( ph -> ps ) -> A. x ( ph -> ps ) )

  proof
    wph
    wps
    vx
    hbim.1
    wps
    wps
    vx
    wal
    wi
    wph
    hbim.2
    a1i
    hbim1
end
