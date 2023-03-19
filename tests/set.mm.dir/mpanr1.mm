include "anassrs.mm"
include "mpanl2.mm"

theorem mpanr1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpanr1.1: |- ps
  assume mpanr1.2: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ( ph /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    mpanr1.1
    wph
    wps
    wch
    wth
    mpanr1.2
    anassrs
    mpanl2
end
