include "wn.mm"
include "con3d.mm"
include "imp.mm"

theorem con3dimp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume con3dimp.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ( ph /\ -. ch ) -> -. ps )

  proof
    wph
    wch
    wn
    wps
    wn
    wph
    wps
    wch
    con3dimp.1
    con3d
    imp
end
