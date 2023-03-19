include "wa.mm"
include "an12.mm"
include "anass.mm"
include "ancom.mm"
include "3bitr2i.mm"

theorem an13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ch /\ ( ps /\ ph ) ) )

  proof
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
    wps
    wph
    wa
    #
    wch
    wa
    wch
    @0
    wa
    wph
    wps
    wch
    an12
    wps
    wph
    wch
    anass
    @0
    wch
    ancom
    3bitr2i
end
