include "wa.mm"
include "wi.mm"
include "biimpi.mm"
include "3impia.mm"

theorem bi13impia
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bi13impia.1: |- ( ( ph /\ ps ) <-> ( ch -> th ) )


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
    wth
    wi
    bi13impia.1
    biimpi
    3impia
end
