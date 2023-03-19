include "wi.mm"
include "syl.mm"
include "syl6d.mm"

theorem ee13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee13.1: |- ( ph -> ps )
  assume ee13.2: |- ( ph -> ( ch -> ( th -> ta ) ) )
  assume ee13.3: |- ( ps -> ( ta -> et ) )


  assert |- ( ph -> ( ch -> ( th -> et ) ) )

  proof
    wph
    wch
    wth
    wta
    wet
    ee13.2
    wph
    wps
    wta
    wet
    wi
    ee13.1
    ee13.3
    syl
    syl6d
end
