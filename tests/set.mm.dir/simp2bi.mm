include "w3a.mm"
include "biimpi.mm"
include "simp2d.mm"

theorem simp2bi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3simp1bi.1: |- ( ph <-> ( ps /\ ch /\ th ) )


  assert |- ( ph -> ch )

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
    simp2d
end
