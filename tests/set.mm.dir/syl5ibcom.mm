include "syl5ib.mm"
include "com12.mm"

theorem syl5ibcom
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume syl5ib.1: |- ( ph -> ps )
  assume syl5ib.2: |- ( ch -> ( ps <-> th ) )


  assert |- ( ph -> ( ch -> th ) )

  proof
    wch
    wph
    wth
    wph
    wps
    wch
    wth
    syl5ib.1
    syl5ib.2
    syl5ib
    com12
end
