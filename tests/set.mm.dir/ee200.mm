include "wi.mm"
include "a1i.mm"
include "ee222.mm"

theorem ee200
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee200.1: |- ( ph -> ( ps -> ch ) )
  assume ee200.2: |- th
  assume ee200.3: |- ta
  assume ee200.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- ( ph -> ( ps -> et ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    ee200.1
    wps
    wth
    wi
    wph
    wth
    wps
    ee200.2
    a1i
    a1i
    wps
    wta
    wi
    wph
    wta
    wps
    ee200.3
    a1i
    a1i
    ee200.4
    ee222
end
