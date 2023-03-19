include "a1d.mm"
include "wi.mm"
include "a1i.mm"
include "ee222.mm"

theorem ee210
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee210.1: |- ( ph -> ( ps -> ch ) )
  assume ee210.2: |- ( ph -> th )
  assume ee210.3: |- ta
  assume ee210.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- ( ph -> ( ps -> et ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    ee210.1
    wph
    wth
    wps
    ee210.2
    a1d
    wps
    wta
    wi
    wph
    wta
    wps
    ee210.3
    a1i
    a1i
    ee210.4
    ee222
end
