include "biimpi.mm"
include "syl6.mm"

theorem syl6ib
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume syl6ib.1: |- ( ph -> ( ps -> ch ) )
  assume syl6ib.2: |- ( ch <-> th )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wth
    syl6ib.1
    wch
    wth
    syl6ib.2
    biimpi
    syl6
end
