include "w3a.mm"
include "3anim1i.mm"
include "sylan.mm"

theorem syl3anl1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume syl3anl1.1: |- ( ph -> ps )
  assume syl3anl1.2: |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et )


  assert |- ( ( ( ph /\ ch /\ th ) /\ ta ) -> et )

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
    wet
    wph
    wps
    wch
    wth
    syl3anl1.1
    3anim1i
    syl3anl1.2
    sylan
end
