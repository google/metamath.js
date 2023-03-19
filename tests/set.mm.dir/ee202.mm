include "wi.mm"
include "a1i.mm"
include "ee222.mm"

theorem ee202
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee202.1: |- ( ph -> ( ps -> ch ) )
  assume ee202.2: |- th
  assume ee202.3: |- ( ph -> ( ps -> ta ) )
  assume ee202.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- ( ph -> ( ps -> et ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    ee202.1
    wps
    wth
    wi
    wph
    wth
    wps
    ee202.2
    a1i
    a1i
    ee202.3
    ee202.4
    ee222
end
