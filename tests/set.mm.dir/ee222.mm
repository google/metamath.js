include "wa.mm"
include "imp.mm"
include "syl3c.mm"
include "ex.mm"

theorem ee222
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee222.1: |- ( ph -> ( ps -> ch ) )
  assume ee222.2: |- ( ph -> ( ps -> th ) )
  assume ee222.3: |- ( ph -> ( ps -> ta ) )
  assume ee222.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- ( ph -> ( ps -> et ) )

  proof
    wph
    wps
    wet
    wph
    wps
    wa
    wch
    wth
    wta
    wet
    wph
    wps
    wch
    ee222.1
    imp
    wph
    wps
    wth
    ee222.2
    imp
    wph
    wps
    wta
    ee222.3
    imp
    ee222.4
    syl3c
    ex
end
