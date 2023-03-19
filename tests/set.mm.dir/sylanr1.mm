include "wa.mm"
include "anim1i.mm"
include "sylan2.mm"

theorem sylanr1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume sylanr1.1: |- ( ph -> ch )
  assume sylanr1.2: |- ( ( ps /\ ( ch /\ th ) ) -> ta )


  assert |- ( ( ps /\ ( ph /\ th ) ) -> ta )

  proof
    wph
    wth
    wa
    wps
    wch
    wth
    wa
    wta
    wph
    wch
    wth
    sylanr1.1
    anim1i
    sylanr1.2
    sylan2
end
