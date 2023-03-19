include "a1d.mm"
include "ee222.mm"

theorem ee112
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee112.1: |- ( ph -> ps )
  assume ee112.2: |- ( ph -> ch )
  assume ee112.3: |- ( ph -> ( th -> ta ) )
  assume ee112.4: |- ( ps -> ( ch -> ( ta -> et ) ) )


  assert |- ( ph -> ( th -> et ) )

  proof
    wph
    wth
    wps
    wch
    wta
    wet
    wph
    wps
    wth
    ee112.1
    a1d
    wph
    wch
    wth
    ee112.2
    a1d
    ee112.3
    ee112.4
    ee222
end
