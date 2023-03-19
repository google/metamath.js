include "syl5com.mm"
include "com12.mm"

theorem syl5
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume syl5.1: |- ( ph -> ps )
  assume syl5.2: |- ( ch -> ( ps -> th ) )


  assert |- ( ch -> ( ph -> th ) )

  proof
    wph
    wch
    wth
    wph
    wps
    wch
    wth
    syl5.1
    syl5.2
    syl5com
    com12
end
