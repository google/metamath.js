include "a1d.mm"
include "wi.mm"
include "a1i.mm"
include "ee222.mm"

theorem ee120
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee120.1: |- ( ph -> ps )
  assume ee120.2: |- ( ph -> ( ch -> th ) )
  assume ee120.3: |- ta
  assume ee120.4: |- ( ps -> ( th -> ( ta -> et ) ) )


  assert |- ( ph -> ( ch -> et ) )

  proof
    wph
    wch
    wps
    wth
    wta
    wet
    wph
    wps
    wch
    ee120.1
    a1d
    ee120.2
    wch
    wta
    wi
    wph
    wta
    wch
    ee120.3
    a1i
    a1i
    ee120.4
    ee222
end
