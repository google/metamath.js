include "ex.mm"
include "syl6ci.mm"

theorem ee21an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ee21an.1: |- ( ph -> ( ps -> ch ) )
  assume ee21an.2: |- ( ph -> th )
  assume ee21an.3: |- ( ( ch /\ th ) -> ta )


  assert |- ( ph -> ( ps -> ta ) )

  proof
    wph
    wps
    wch
    wth
    wta
    ee21an.1
    ee21an.2
    wch
    wth
    wta
    ee21an.3
    ex
    syl6ci
end
