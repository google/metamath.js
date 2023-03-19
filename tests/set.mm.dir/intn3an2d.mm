include "w3a.mm"
include "simp2.mm"
include "nsyl.mm"

theorem intn3an2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume intn3and.1: |- ( ph -> -. ps )


  assert |- ( ph -> -. ( ch /\ ps /\ th ) )

  proof
    wph
    wps
    wch
    wps
    wth
    w3a
    intn3and.1
    wch
    wps
    wth
    simp2
    nsyl
end
