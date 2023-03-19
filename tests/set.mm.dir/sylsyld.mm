include "wi.mm"
include "syl.mm"
include "syld.mm"

theorem sylsyld
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume sylsyld.1: |- ( ph -> ps )
  assume sylsyld.2: |- ( ph -> ( ch -> th ) )
  assume sylsyld.3: |- ( ps -> ( th -> ta ) )


  assert |- ( ph -> ( ch -> ta ) )

  proof
    wph
    wch
    wth
    wta
    sylsyld.2
    wph
    wps
    wth
    wta
    wi
    sylsyld.1
    sylsyld.3
    syl
    syld
end
