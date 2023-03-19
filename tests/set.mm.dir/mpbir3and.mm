include "w3a.mm"
include "3jca.mm"
include "mpbird.mm"

theorem mpbir3and
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume mpbir3and.1: |- ( ph -> ch )
  assume mpbir3and.2: |- ( ph -> th )
  assume mpbir3and.3: |- ( ph -> ta )
  assume mpbir3and.4: |- ( ph -> ( ps <-> ( ch /\ th /\ ta ) ) )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wch
    wth
    wta
    w3a
    wph
    wch
    wth
    wta
    mpbir3and.1
    mpbir3and.2
    mpbir3and.3
    3jca
    mpbir3and.4
    mpbird
end
