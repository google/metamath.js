include "wa.mm"
include "biimpd.mm"
include "3impib.mm"

theorem bi23impib
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bi23impib.1: |- ( ph -> ( ( ps /\ ch ) <-> th ) )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wa
    wth
    bi23impib.1
    biimpd
    3impib
end
