include "a1d.mm"
include "wi.mm"
include "a1i.mm"
include "ee222.mm"

theorem ee102
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee102.1: |- ( ph -> ps )
  assume ee102.2: |- ch
  assume ee102.3: |- ( ph -> ( th -> ta ) )
  assume ee102.4: |- ( ps -> ( ch -> ( ta -> et ) ) )


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
    ee102.1
    a1d
    wth
    wch
    wi
    wph
    wch
    wth
    ee102.2
    a1i
    a1i
    ee102.3
    ee102.4
    ee222
end
