include "wa.mm"
include "jctl.mm"
include "sylan.mm"

theorem mpanl1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpanl1.1: |- ph
  assume mpanl1.2: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


  assert |- ( ( ps /\ ch ) -> th )

  proof
    wps
    wph
    wps
    wa
    wch
    wth
    wps
    wph
    mpanl1.1
    jctl
    mpanl1.2
    sylan
end
