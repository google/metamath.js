include "w3a.mm"
include "biimpi.mm"
include "simp3d.mm"

theorem simp3bi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3simp1bi.1: |- ( ph <-> ( ps /\ ch /\ th ) )


  assert |- ( ph -> th )

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
    simp3d
end
