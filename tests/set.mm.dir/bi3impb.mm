include "wa.mm"
include "biimpi.mm"
include "3impb.mm"

theorem bi3impb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bi3impb.1: |- ( ( ph /\ ( ps /\ ch ) ) <-> th )


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
    wa
    wth
    bi3impb.1
    biimpi
    3impb
end
