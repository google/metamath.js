include "w3a.mm"
include "3adant3.mm"
include "simp1.mm"
include "simp3.mm"
include "syl3anc.mm"

theorem stoic4a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume stoic4a.1: |- ( ( ph /\ ps ) -> ch )
  assume stoic4a.2: |- ( ( ch /\ ph /\ th ) -> ta )


  assert |- ( ( ph /\ ps /\ th ) -> ta )

  proof
    wph
    wps
    wth
    w3a
    wch
    wph
    wth
    wta
    wph
    wps
    wch
    wth
    stoic4a.1
    3adant3
    wph
    wps
    wth
    simp1
    wph
    wps
    wth
    simp3
    stoic4a.2
    syl3anc
end
