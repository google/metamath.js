include "syl6.mm"
include "com12.mm"

theorem syl6com
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume syl6com.1: |- ( ph -> ( ps -> ch ) )
  assume syl6com.2: |- ( ch -> th )


  assert |- ( ps -> ( ph -> th ) )

  proof
    wph
    wps
    wth
    wph
    wps
    wch
    wth
    syl6com.1
    syl6com.2
    syl6
    com12
end
