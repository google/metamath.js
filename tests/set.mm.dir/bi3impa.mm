include "wa.mm"
include "biimpi.mm"
include "3impa.mm"

theorem bi3impa
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bi3impa.1: |- ( ( ( ph /\ ps ) /\ ch ) <-> th )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wa
    wch
    wa
    wth
    bi3impa.1
    biimpi
    3impa
end
