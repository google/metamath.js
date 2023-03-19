include "wa.mm"
include "jctr.mm"
include "sylan2.mm"

theorem mpanr2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpanr2.1: |- ch
  assume mpanr2.2: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ( ph /\ ps ) -> th )

  proof
    wps
    wph
    wps
    wch
    wa
    wth
    wps
    wch
    mpanr2.1
    jctr
    mpanr2.2
    sylan2
end
