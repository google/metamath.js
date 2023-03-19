include "wi.mm"
include "a1i.mm"
include "a1d.mm"
include "ee222.mm"

theorem ee201
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee201.1: |- ( ph -> ( ps -> ch ) )
  assume ee201.2: |- th
  assume ee201.3: |- ( ph -> ta )
  assume ee201.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- ( ph -> ( ps -> et ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    ee201.1
    wps
    wth
    wi
    wph
    wth
    wps
    ee201.2
    a1i
    a1i
    wph
    wta
    wps
    ee201.3
    a1d
    ee201.4
    ee222
end
