include "syl.mm"

theorem 3syl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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
