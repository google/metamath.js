include "w3a.mm"
include "3anim1i.mm"
include "sylan2.mm"

theorem syl3anr1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume syl3anr1.1: |- ( ph -> ps )
  assume syl3anr1.2: |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et )


  assert |- ( ( ch /\ ( ph /\ th /\ ta ) ) -> et )

  proof
    wph
    wth
    wta
    w3a
    wch
    wps
    wth
    wta
    w3a
    wet
    wph
    wps
    wth
    wta
    syl3anr1.1
    3anim1i
    syl3anr1.2
    sylan2
end
