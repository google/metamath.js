include "ex.mm"
include "mpsylsyld.mm"

theorem ee02an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ee02an.1: |- ph
  assume ee02an.2: |- ( ps -> ( ch -> th ) )
  assume ee02an.3: |- ( ( ph /\ th ) -> ta )


  assert |- ( ps -> ( ch -> ta ) )

  proof
    wph
    wps
    wch
    wth
    wta
    ee02an.1
    ee02an.2
    wph
    wth
    wta
    ee02an.3
    ex
    mpsylsyld
end
