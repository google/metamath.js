include "3syl.mm"
include "syl.mm"

theorem 4syl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
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
