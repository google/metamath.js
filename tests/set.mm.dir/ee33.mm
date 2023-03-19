include "wi.mm"
include "imim3i.mm"
include "syl6c.mm"

theorem ee33
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee33.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume ee33.2: |- ( ph -> ( ps -> ( ch -> ta ) ) )
  assume ee33.3: |- ( th -> ( ta -> et ) )


  assert |- ( ph -> ( ps -> ( ch -> et ) ) )

  proof
    wph
    wps
    wch
    wth
    wi
    wch
    wta
    wi
    wch
    wet
    wi
    ee33.1
    ee33.2
    wth
    wta
    wet
    wch
    ee33.3
    imim3i
    syl6c
end
