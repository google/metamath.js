include "wa.mm"
include "w3a.mm"
include "ancom.mm"
include "3anass.mm"
include "df-3an.mm"
include "3bitr4i.mm"

theorem 3anrot
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ch /\ ph ) )

  proof
    wph
    wps
    wch
    wa
    #
    wa
    @0
    wph
    wa
    wph
    wps
    wch
    w3a
    wps
    wch
    wph
    w3a
    wph
    @0
    ancom
    wph
    wps
    wch
    3anass
    wps
    wch
    wph
    df-3an
    3bitr4i
end
