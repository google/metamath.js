include "2a1i.mm"
include "ee222.mm"

theorem ee220
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee220.1: |- ( ph -> ( ps -> ch ) )
  assume ee220.2: |- ( ph -> ( ps -> th ) )
  assume ee220.3: |- ta
  assume ee220.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- ( ph -> ( ps -> et ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    ee220.1
    ee220.2
    wta
    wph
    wps
    ee220.3
    2a1i
    ee220.4
    ee222
end
