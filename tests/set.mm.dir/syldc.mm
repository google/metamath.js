include "syld.mm"
include "com12.mm"

theorem syldc
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume syld.1: |- ( ph -> ( ps -> ch ) )
  assume syld.2: |- ( ph -> ( ch -> th ) )


  assert |- ( ps -> ( ph -> th ) )

  proof
    wph
    wps
    wth
    wph
    wps
    wch
    wth
    syld.1
    syld.2
    syld
    com12
end
