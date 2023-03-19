include "wa.mm"
include "an13.mm"
include "anass.mm"
include "3bitr4i.mm"

theorem an31
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ch /\ ps ) /\ ph ) )

  proof
    wph
    wps
    wch
    wa
    wa
    wch
    wps
    wph
    wa
    wa
    wph
    wps
    wa
    wch
    wa
    wch
    wps
    wa
    wph
    wa
    wph
    wps
    wch
    an13
    wph
    wps
    wch
    anass
    wch
    wps
    wph
    anass
    3bitr4i
end
