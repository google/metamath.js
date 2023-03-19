include "w3a.mm"
include "simp3.mm"
include "nsyl.mm"

theorem intn3an3d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume intn3and.1: |- ( ph -> -. ps )


  assert |- ( ph -> -. ( ch /\ th /\ ps ) )

  proof
    wph
    wps
    wch
    wth
    wps
    w3a
    intn3and.1
    wch
    wth
    wps
    simp3
    nsyl
end
