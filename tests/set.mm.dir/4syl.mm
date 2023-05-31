include "3syl.mm"
include "syl.mm"

theorem 4syl
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume 4syl.1: |- ( ph -> ps )
  assume 4syl.2: |- ( ps -> ch )
  assume 4syl.3: |- ( ch -> th )
  assume 4syl.4: |- ( th -> ta )


  assert |- ( ph -> ta )

  proof
    wph
    wth
    wta
    wph
    wps
    wch
    wth
    4syl.1
    4syl.2
    4syl.3
    3syl
    4syl.4
    syl
end
