include "w3a.mm"
include "simp1.mm"
include "nsyl.mm"

theorem intn3an1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume intn3and.1: |- ( ph -> -. ps )


  assert |- ( ph -> -. ( ps /\ ch /\ th ) )

  proof
    wph
    wps
    wps
    wch
    wth
    w3a
    intn3and.1
    wps
    wch
    wth
    simp1
    nsyl
end
