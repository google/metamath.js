include "wn.mm"
include "a1i.mm"
include "mt3d.mm"

theorem mt3i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mt3i.1: |- -. ch
  assume mt3i.2: |- ( ph -> ( -. ps -> ch ) )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wch
    wch
    wn
    wph
    mt3i.1
    a1i
    mt3i.2
    mt3d
end
