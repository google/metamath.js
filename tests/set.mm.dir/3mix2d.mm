include "w3o.mm"
include "3mix2.mm"
include "syl.mm"

theorem 3mix2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3mixd.1: |- ( ph -> ps )


  assert |- ( ph -> ( ch \/ ps \/ th ) )

  proof
    wph
    wps
    wch
    wps
    wth
    w3o
    3mixd.1
    wps
    wch
    wth
    3mix2
    syl
end
