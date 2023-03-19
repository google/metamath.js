include "wa.mm"
include "anass.mm"
include "an12.mm"
include "ancom.mm"
include "3bitri.mm"

theorem an32
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ph /\ ch ) /\ ps ) )

  proof
    wph
    wps
    wa
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
    #
    wa
    @0
    wps
    wa
    wph
    wps
    wch
    anass
    wph
    wps
    wch
    an12
    wps
    @0
    ancom
    3bitri
end
