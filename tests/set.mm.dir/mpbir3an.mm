include "w3a.mm"
include "3pm3.2i.mm"
include "mpbir.mm"

theorem mpbir3an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpbir3an.1: |- ps
  assume mpbir3an.2: |- ch
  assume mpbir3an.3: |- th
  assume mpbir3an.4: |- ( ph <-> ( ps /\ ch /\ th ) )


  assert |- ph

  proof
    wph
    wps
    wch
    wth
    w3a
    wps
    wch
    wth
    mpbir3an.1
    mpbir3an.2
    mpbir3an.3
    3pm3.2i
    mpbir3an.4
    mpbir
end
