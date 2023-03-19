include "w3a.mm"
include "3anim3i.mm"
include "sylan.mm"

theorem syl3anl3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume syl3anl3.1: |- ( ph -> th )
  assume syl3anl3.2: |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et )


  assert |- ( ( ( ps /\ ch /\ ph ) /\ ta ) -> et )

  proof
    wps
    wch
    wph
    w3a
    wps
    wch
    wth
    w3a
    wta
    wet
    wph
    wth
    wps
    wch
    syl3anl3.1
    3anim3i
    syl3anl3.2
    sylan
end
