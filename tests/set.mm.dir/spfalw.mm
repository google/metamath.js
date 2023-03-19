include "wn.mm"
include "hbth.mm"
include "spnfw.mm"

theorem spfalw
  let wph: wff ph
  let vx: setvar x
  assume spfalw.1: |- -. ph


  assert |- ( A. x ph -> ph )

  proof
    wph
    vx
    wph
    wn
    vx
    spfalw.1
    hbth
    spnfw
end
