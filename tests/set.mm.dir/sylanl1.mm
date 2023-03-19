include "wa.mm"
include "anim1i.mm"
include "sylan.mm"

theorem sylanl1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume sylanl1.1: |- ( ph -> ps )
  assume sylanl1.2: |- ( ( ( ps /\ ch ) /\ th ) -> ta )


  assert |- ( ( ( ph /\ ch ) /\ th ) -> ta )

  proof
    wph
    wch
    wa
    wps
    wch
    wa
    wth
    wta
    wph
    wps
    wch
    sylanl1.1
    anim1i
    sylanl1.2
    sylan
end
