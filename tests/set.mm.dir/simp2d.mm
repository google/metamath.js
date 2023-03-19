include "w3a.mm"
include "simp2.mm"
include "syl.mm"

theorem simp2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3simp1d.1: |- ( ph -> ( ps /\ ch /\ th ) )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    wth
    w3a
    wch
    3simp1d.1
    wps
    wch
    wth
    simp2
    syl
end
