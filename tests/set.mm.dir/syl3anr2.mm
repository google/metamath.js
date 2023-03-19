include "w3a.mm"
include "ancoms.mm"
include "syl3anl2.mm"

theorem syl3anr2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume syl3anr2.1: |- ( ph -> th )
  assume syl3anr2.2: |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et )


  assert |- ( ( ch /\ ( ps /\ ph /\ ta ) ) -> et )

  proof
    wps
    wph
    wta
    w3a
    wch
    wet
    wph
    wps
    wth
    wta
    wch
    wet
    syl3anr2.1
    wch
    wps
    wth
    wta
    w3a
    wet
    syl3anr2.2
    ancoms
    syl3anl2
    ancoms
end
