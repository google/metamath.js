include "w3a.mm"
include "3anim123i.mm"
include "syl.mm"

theorem syl3an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume syl3an.1: |- ( ph -> ps )
  assume syl3an.2: |- ( ch -> th )
  assume syl3an.3: |- ( ta -> et )
  assume syl3an.4: |- ( ( ps /\ th /\ et ) -> ze )


  assert |- ( ( ph /\ ch /\ ta ) -> ze )

  proof
    wph
    wch
    wta
    w3a
    wps
    wth
    wet
    w3a
    wze
    wph
    wps
    wch
    wth
    wta
    wet
    syl3an.1
    syl3an.2
    syl3an.3
    3anim123i
    syl3an.4
    syl
end
