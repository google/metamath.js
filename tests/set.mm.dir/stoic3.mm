include "wa.mm"
include "sylan.mm"
include "3impa.mm"

theorem stoic3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume stoic3.1: |- ( ( ph /\ ps ) -> ch )
  assume stoic3.2: |- ( ( ch /\ th ) -> ta )


  assert |- ( ( ph /\ ps /\ th ) -> ta )

  proof
    wph
    wps
    wth
    wta
    wph
    wps
    wa
    wch
    wth
    wta
    stoic3.1
    stoic3.2
    sylan
    3impa
end
