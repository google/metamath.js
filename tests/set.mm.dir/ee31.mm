include "wi.mm"
include "a1d.mm"
include "ee33.mm"

theorem ee31
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee31.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume ee31.2: |- ( ph -> ta )
  assume ee31.3: |- ( th -> ( ta -> et ) )


  assert |- ( ph -> ( ps -> ( ch -> et ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    ee31.1
    wph
    wch
    wta
    wi
    wps
    wph
    wta
    wch
    ee31.2
    a1d
    a1d
    ee31.3
    ee33
end
