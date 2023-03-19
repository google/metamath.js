include "wi.mm"
include "a1i.mm"
include "ee222.mm"

theorem ee020
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee020.1: |- ph
  assume ee020.2: |- ( ps -> ( ch -> th ) )
  assume ee020.3: |- ta
  assume ee020.4: |- ( ph -> ( th -> ( ta -> et ) ) )


  assert |- ( ps -> ( ch -> et ) )

  proof
    wps
    wch
    wph
    wth
    wta
    wet
    wch
    wph
    wi
    wps
    wph
    wch
    ee020.1
    a1i
    a1i
    ee020.2
    wch
    wta
    wi
    wps
    wta
    wch
    ee020.3
    a1i
    a1i
    ee020.4
    ee222
end
