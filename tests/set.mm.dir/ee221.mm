include "a1d.mm"
include "ee222.mm"

theorem ee221
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee221.1: |- ( ph -> ( ps -> ch ) )
  assume ee221.2: |- ( ph -> ( ps -> th ) )
  assume ee221.3: |- ( ph -> ta )
  assume ee221.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- ( ph -> ( ps -> et ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    ee221.1
    ee221.2
    wph
    wta
    wps
    ee221.3
    a1d
    ee221.4
    ee222
end
