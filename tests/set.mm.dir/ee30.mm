include "wi.mm"
include "a1i.mm"
include "ee33.mm"

theorem ee30
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee30.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume ee30.2: |- ta
  assume ee30.3: |- ( th -> ( ta -> et ) )


  assert |- ( ph -> ( ps -> ( ch -> et ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    ee30.1
    wps
    wch
    wta
    wi
    #
    wi
    wph
    @0
    wps
    wta
    wch
    ee30.2
    a1i
    a1i
    a1i
    ee30.3
    ee33
end
