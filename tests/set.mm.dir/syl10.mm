include "wi.mm"
include "syl6.mm"
include "syldd.mm"

theorem syl10
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume syl10.1: |- ( ph -> ( ps -> ch ) )
  assume syl10.2: |- ( ph -> ( ps -> ( th -> ta ) ) )
  assume syl10.3: |- ( ch -> ( ta -> et ) )


  assert |- ( ph -> ( ps -> ( th -> et ) ) )

  proof
    wph
    wps
    wth
    wta
    wet
    syl10.2
    wph
    wps
    wch
    wta
    wet
    wi
    syl10.1
    syl10.3
    syl6
    syldd
end
