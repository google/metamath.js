include "wi.mm"
include "a1i.mm"
include "a1d.mm"
include "ee222.mm"

theorem ee021
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee021.1: |- ph
  assume ee021.2: |- ( ps -> ( ch -> th ) )
  assume ee021.3: |- ( ps -> ta )
  assume ee021.4: |- ( ph -> ( th -> ( ta -> et ) ) )


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
    ee021.1
    a1i
    a1i
    ee021.2
    wps
    wta
    wch
    ee021.3
    a1d
    ee021.4
    ee222
end
