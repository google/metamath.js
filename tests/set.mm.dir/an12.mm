include "wa.mm"
include "ancom.mm"
include "anbi1i.mm"
include "anass.mm"
include "3bitr3i.mm"

theorem an12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ps /\ ( ph /\ ch ) ) )

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
    wa
    wa
    wps
    wph
    wch
    wa
    wa
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
    anass
    wps
    wph
    wch
    anass
    3bitr3i
end
