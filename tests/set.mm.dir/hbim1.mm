include "wi.mm"
include "wal.mm"
include "a2i.mm"
include "19.21h.mm"
include "sylibr.mm"

theorem hbim1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume hbim1.1: |- ( ph -> A. x ph )
  assume hbim1.2: |- ( ph -> ( ps -> A. x ps ) )


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
    hbim1.2
    a2i
    wph
    wps
    vx
    hbim1.1
    19.21h
    sylibr
end
