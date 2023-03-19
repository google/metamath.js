include "w3o.mm"
include "3mix1.mm"
include "syl.mm"

theorem 3mix1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3mixd.1: |- ( ph -> ps )


  assert |- ( ph -> ( ps \/ ch \/ th ) )

  proof
    wph
    wps
    wps
    wch
    wth
    w3o
    3mixd.1
    wps
    wch
    wth
    3mix1
    syl
end
