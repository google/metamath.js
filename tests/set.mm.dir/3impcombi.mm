include "wi.mm"
include "w3a.mm"
include "biimpd.mm"
include "3anidm13.mm"
include "ancoms.mm"
include "3impia.mm"

theorem 3impcombi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3impcombi.1: |- ( ( ph /\ ps /\ ph ) -> ( ch <-> th ) )


  assert |- ( ( ps /\ ph /\ ch ) -> th )

  proof
    wps
    wph
    wch
    wth
    wph
    wps
    wch
    wth
    wi
    #
    wph
    wps
    @0
    wph
    wps
    wph
    w3a
    wch
    wth
    3impcombi.1
    biimpd
    3anidm13
    ancoms
    3impia
end
