include "a1d.mm"
include "sylcom.mm"

theorem syl5com
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume syl5com.1: |- ( ph -> ps )
  assume syl5com.2: |- ( ch -> ( ps -> th ) )


  assert |- ( ph -> ( ch -> th ) )

  proof
    wph
    wch
    wps
    wth
    wph
    wps
    wch
    syl5com.1
    a1d
    syl5com.2
    sylcom
end
