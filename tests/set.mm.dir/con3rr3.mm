include "wn.mm"
include "con3d.mm"
include "com12.mm"

theorem con3rr3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume con3rr3.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( -. ch -> ( ph -> -. ps ) )

  proof
    wph
    wch
    wn
    wps
    wn
    wph
    wps
    wch
    con3rr3.1
    con3d
    com12
end
