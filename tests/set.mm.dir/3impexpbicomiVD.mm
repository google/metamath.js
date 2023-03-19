include "w3a.mm"
include "wb.mm"
include "wi.mm"
include "3impexpbicom.mm"
include "biimpi.mm"
include "e0a.mm"

theorem 3impexpbicomiVD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3impexpbicomiVD.1: |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) )


  assert |- ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) )

  proof
    wph
    wps
    wch
    w3a
    wth
    wta
    wb
    wi
    #
    wph
    wps
    wch
    wta
    wth
    wb
    wi
    wi
    wi
    #
    3impexpbicomiVD.1
    @0
    @1
    wph
    wps
    wch
    wth
    wta
    3impexpbicom
    biimpi
    e0a
end
