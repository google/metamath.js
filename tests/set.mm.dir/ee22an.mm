include "ex.mm"
include "syl6c.mm"

theorem ee22an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ee22an.1: |- ( ph -> ( ps -> ch ) )
  assume ee22an.2: |- ( ph -> ( ps -> th ) )
  assume ee22an.3: |- ( ( ch /\ th ) -> ta )


  assert |- ( ph -> ( ps -> ta ) )

  proof
    wph
    wps
    wch
    wth
    wta
    ee22an.1
    ee22an.2
    wch
    wth
    wta
    ee22an.3
    ex
    syl6c
end
