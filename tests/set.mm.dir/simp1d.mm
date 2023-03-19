include "w3a.mm"
include "simp1.mm"
include "syl.mm"

theorem simp1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3simp1d.1: |- ( ph -> ( ps /\ ch /\ th ) )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wch
    wth
    w3a
    wps
    3simp1d.1
    wps
    wch
    wth
    simp1
    syl
end
