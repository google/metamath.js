include "wi.mm"
include "a1i.mm"
include "ee222.mm"

theorem ee022
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee022.1: |- ph
  assume ee022.2: |- ( ps -> ( ch -> th ) )
  assume ee022.3: |- ( ps -> ( ch -> ta ) )
  assume ee022.4: |- ( ph -> ( th -> ( ta -> et ) ) )


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
    ee022.1
    a1i
    a1i
    ee022.2
    ee022.3
    ee022.4
    ee222
end
