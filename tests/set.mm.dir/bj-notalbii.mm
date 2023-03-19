include "wn.mm"
include "notbii.mm"
include "albii.mm"

theorem bj-notalbii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume bj-notalbii.1: |- ( ph <-> ps )


  assert |- ( A. x -. ph <-> A. x -. ps )

  proof
    wph
    wn
    wps
    wn
    vx
    wph
    wps
    bj-notalbii.1
    notbii
    albii
end
