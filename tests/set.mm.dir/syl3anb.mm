include "w3a.mm"
include "3anbi123i.mm"
include "sylbi.mm"

theorem syl3anb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume syl3anb.1: |- ( ph <-> ps )
  assume syl3anb.2: |- ( ch <-> th )
  assume syl3anb.3: |- ( ta <-> et )
  assume syl3anb.4: |- ( ( ps /\ th /\ et ) -> ze )


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
    syl3anb.1
    syl3anb.2
    syl3anb.3
    3anbi123i
    syl3anb.4
    sylbi
end
