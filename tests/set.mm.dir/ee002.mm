include "wi.mm"
include "a1i.mm"
include "ee222.mm"

theorem ee002
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee002.1: |- ph
  assume ee002.2: |- ps
  assume ee002.3: |- ( ch -> ( th -> ta ) )
  assume ee002.4: |- ( ph -> ( ps -> ( ta -> et ) ) )


  assert |- ( ch -> ( th -> et ) )

  proof
    wch
    wth
    wph
    wps
    wta
    wet
    wth
    wph
    wi
    wch
    wph
    wth
    ee002.1
    a1i
    a1i
    wth
    wps
    wi
    wch
    wps
    wth
    ee002.2
    a1i
    a1i
    ee002.3
    ee002.4
    ee222
end
