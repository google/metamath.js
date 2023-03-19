include "w3a.mm"
include "biimpi.mm"
include "simp1d.mm"

theorem simp1bi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3simp1bi.1: |- ( ph <-> ( ps /\ ch /\ th ) )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    w3a
    3simp1bi.1
    biimpi
    simp1d
end
