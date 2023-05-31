include "syl.mm"

theorem 3syl
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume 3syl.1: |- ( ph -> ps )
  assume 3syl.2: |- ( ps -> ch )
  assume 3syl.3: |- ( ch -> th )


  assert |- ( ph -> th )

  proof
    wph
    wch
    wth
    wph
    wps
    wch
    3syl.1
    3syl.2
    syl
    3syl.3
    syl
end
