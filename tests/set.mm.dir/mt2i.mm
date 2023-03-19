include "a1i.mm"
include "mt2d.mm"

theorem mt2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mt2i.1: |- ch
  assume mt2i.2: |- ( ph -> ( ps -> -. ch ) )


  assert |- ( ph -> -. ps )

  proof
    wph
    wps
    wch
    wch
    wph
    mt2i.1
    a1i
    mt2i.2
    mt2d
end
