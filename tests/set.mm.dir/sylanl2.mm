include "wa.mm"
include "anim2i.mm"
include "sylan.mm"

theorem sylanl2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume sylanl2.1: |- ( ph -> ch )
  assume sylanl2.2: |- ( ( ( ps /\ ch ) /\ th ) -> ta )


  assert |- ( ( ( ps /\ ph ) /\ th ) -> ta )

  proof
    wps
    wph
    wa
    wps
    wch
    wa
    wth
    wta
    wph
    wch
    wps
    sylanl2.1
    anim2i
    sylanl2.2
    sylan
end
