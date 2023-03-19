include "wa.mm"
include "anim2i.mm"
include "sylan2.mm"

theorem sylanr2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume sylanr2.1: |- ( ph -> th )
  assume sylanr2.2: |- ( ( ps /\ ( ch /\ th ) ) -> ta )


  assert |- ( ( ps /\ ( ch /\ ph ) ) -> ta )

  proof
    wch
    wph
    wa
    wps
    wch
    wth
    wa
    wta
    wph
    wth
    wch
    sylanr2.1
    anim2i
    sylanr2.2
    sylan2
end
