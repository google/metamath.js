include "w3a.mm"
include "simp3.mm"
include "syl.mm"

theorem simp3d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3simp1d.1: |- ( ph -> ( ps /\ ch /\ th ) )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wch
    wth
    w3a
    wth
    3simp1d.1
    wps
    wch
    wth
    simp3
    syl
end
