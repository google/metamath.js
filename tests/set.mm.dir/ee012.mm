include "wi.mm"
include "a1i.mm"
include "a1d.mm"
include "ee222.mm"

theorem ee012
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee012.1: |- ph
  assume ee012.2: |- ( ps -> ch )
  assume ee012.3: |- ( ps -> ( th -> ta ) )
  assume ee012.4: |- ( ph -> ( ch -> ( ta -> et ) ) )


  assert |- ( ps -> ( th -> et ) )

  proof
    wps
    wth
    wph
    wch
    wta
    wet
    wth
    wph
    wi
    wps
    wph
    wth
    ee012.1
    a1i
    a1i
    wps
    wch
    wth
    ee012.2
    a1d
    ee012.3
    ee012.4
    ee222
end
