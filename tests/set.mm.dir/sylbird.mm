include "biimprd.mm"
include "syld.mm"

theorem sylbird
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume sylbird.1: |- ( ph -> ( ch <-> ps ) )
  assume sylbird.2: |- ( ph -> ( ch -> th ) )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wth
    wph
    wch
    wps
    sylbird.1
    biimprd
    sylbird.2
    syld
end
