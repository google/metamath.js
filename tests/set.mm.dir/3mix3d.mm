include "w3o.mm"
include "3mix3.mm"
include "syl.mm"

theorem 3mix3d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3mixd.1: |- ( ph -> ps )


  assert |- ( ph -> ( ch \/ th \/ ps ) )

  proof
    wph
    wps
    wch
    wth
    wps
    w3o
    3mixd.1
    wps
    wch
    wth
    3mix3
    syl
end
