include "syl5ibr.mm"
include "com12.mm"

theorem syl5ibrcom
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume syl5ibr.1: |- ( ph -> th )
  assume syl5ibr.2: |- ( ch -> ( ps <-> th ) )


  assert |- ( ph -> ( ch -> ps ) )

  proof
    wch
    wph
    wps
    wph
    wps
    wch
    wth
    syl5ibr.1
    syl5ibr.2
    syl5ibr
    com12
end
