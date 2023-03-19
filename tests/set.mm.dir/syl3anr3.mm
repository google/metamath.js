include "w3a.mm"
include "3anim3i.mm"
include "sylan2.mm"

theorem syl3anr3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume syl3anr3.1: |- ( ph -> ta )
  assume syl3anr3.2: |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et )


  assert |- ( ( ch /\ ( ps /\ th /\ ph ) ) -> et )

  proof
    wps
    wth
    wph
    w3a
    wch
    wps
    wth
    wta
    w3a
    wet
    wph
    wta
    wps
    wth
    syl3anr3.1
    3anim3i
    syl3anr3.2
    sylan2
end
