include "wi.mm"
include "wal.mm"
include "a2i.mm"
include "19.21hOLD.mm"
include "sylibr.mm"

theorem hbim1OLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume hbim1OLD.1: |- ( ph -> A. x ph )
  assume hbim1OLD.2: |- ( ph -> ( ps -> A. x ps ) )


  assert |- ( ( ph -> ps ) -> A. x ( ph -> ps ) )

  proof
    wph
    wps
    wi
    #
    wph
    wps
    vx
    wal
    #
    wi
    @0
    vx
    wal
    wph
    wps
    @1
    hbim1OLD.2
    a2i
    wph
    wps
    vx
    hbim1OLD.1
    19.21hOLD
    sylibr
end
