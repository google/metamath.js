include "w3a.mm"
include "3anim1i.mm"
include "syl.mm"

theorem syl3an1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl3an1.1: |- ( ph -> ps )
  assume syl3an1.2: |- ( ( ps /\ ch /\ th ) -> ta )


  assert |- ( ( ph /\ ch /\ th ) -> ta )

  proof
    wph
    wch
    wth
    w3a
    wps
    wch
    wth
    w3a
    wta
    wph
    wps
    wch
    wth
    syl3an1.1
    3anim1i
    syl3an1.2
    syl
end
