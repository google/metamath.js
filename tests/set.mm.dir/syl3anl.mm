include "w3a.mm"
include "3anim123i.mm"
include "sylan.mm"

theorem syl3anl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  assume syl3anl.1: |- ( ph -> ps )
  assume syl3anl.2: |- ( ch -> th )
  assume syl3anl.3: |- ( ta -> et )
  assume syl3anl.4: |- ( ( ( ps /\ th /\ et ) /\ ze ) -> si )


  assert |- ( ( ( ph /\ ch /\ ta ) /\ ze ) -> si )

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
    wsi
    wph
    wps
    wch
    wth
    wta
    wet
    syl3anl.1
    syl3anl.2
    syl3anl.3
    3anim123i
    syl3anl.4
    sylan
end
