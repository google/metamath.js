include "wa.mm"
include "jctr.mm"
include "sylan.mm"

theorem mpanl2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpanl2.1: |- ps
  assume mpanl2.2: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


  assert |- ( ( ph /\ ch ) -> th )

  proof
    wph
    wph
    wps
    wa
    wch
    wth
    wph
    wps
    mpanl2.1
    jctr
    mpanl2.2
    sylan
end
