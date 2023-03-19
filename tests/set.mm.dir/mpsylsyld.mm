include "a1i.mm"
include "sylsyld.mm"

theorem mpsylsyld
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume mpsylsyld.1: |- ph
  assume mpsylsyld.2: |- ( ps -> ( ch -> th ) )
  assume mpsylsyld.3: |- ( ph -> ( th -> ta ) )


  assert |- ( ps -> ( ch -> ta ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wph
    wps
    mpsylsyld.1
    a1i
    mpsylsyld.2
    mpsylsyld.3
    sylsyld
end
