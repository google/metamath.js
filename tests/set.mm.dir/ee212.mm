include "a1d.mm"
include "ee222.mm"

theorem ee212
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee212.1: |- ( ph -> ( ps -> ch ) )
  assume ee212.2: |- ( ph -> th )
  assume ee212.3: |- ( ph -> ( ps -> ta ) )
  assume ee212.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- ( ph -> ( ps -> et ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    ee212.1
    wph
    wth
    wps
    ee212.2
    a1d
    ee212.3
    ee212.4
    ee222
end
