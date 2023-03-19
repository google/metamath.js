include "w3a.mm"
include "3adant3.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "syl31anc.mm"

theorem stoic4b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume stoic4b.1: |- ( ( ph /\ ps ) -> ch )
  assume stoic4b.2: |- ( ( ( ch /\ ph /\ ps ) /\ th ) -> ta )


  assert |- ( ( ph /\ ps /\ th ) -> ta )

  proof
    wph
    wps
    wth
    w3a
    wch
    wph
    wps
    wth
    wta
    wph
    wps
    wch
    wth
    stoic4b.1
    3adant3
    wph
    wps
    wth
    simp1
    wph
    wps
    wth
    simp2
    wph
    wps
    wth
    simp3
    stoic4b.2
    syl31anc
end
