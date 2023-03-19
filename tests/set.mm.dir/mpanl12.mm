include "mpanl1.mm"
include "mpan.mm"

theorem mpanl12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpanl12.1: |- ph
  assume mpanl12.2: |- ps
  assume mpanl12.3: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


  assert |- ( ch -> th )

  proof
    wps
    wch
    wth
    mpanl12.2
    wph
    wps
    wch
    wth
    mpanl12.1
    mpanl12.3
    mpanl1
    mpan
end
