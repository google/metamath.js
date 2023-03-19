include "a1dd.mm"
include "ee33an.mm"

theorem ee23an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee23an.1: |- ( ph -> ( ps -> ch ) )
  assume ee23an.2: |- ( ph -> ( ps -> ( th -> ta ) ) )
  assume ee23an.3: |- ( ( ch /\ ta ) -> et )


  assert |- ( ph -> ( ps -> ( th -> et ) ) )

  proof
    wph
    wps
    wth
    wch
    wta
    wet
    wph
    wps
    wch
    wth
    ee23an.1
    a1dd
    ee23an.2
    ee23an.3
    ee33an
end
