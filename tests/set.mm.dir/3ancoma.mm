include "wa.mm"
include "w3a.mm"
include "ancom.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "3bitr4i.mm"

theorem 3ancoma
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ph /\ ch ) )

  proof
    wph
    wps
    wa
    #
    wch
    wa
    wps
    wph
    wa
    #
    wch
    wa
    wph
    wps
    wch
    w3a
    wps
    wph
    wch
    w3a
    @0
    @1
    wch
    wph
    wps
    ancom
    anbi1i
    wph
    wps
    wch
    df-3an
    wps
    wph
    wch
    df-3an
    3bitr4i
end
