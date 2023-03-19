include "weq.mm"
include "idd.mm"
include "spimw.mm"

theorem spnfw
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume spnfw.1: |- ( -. ph -> A. x -. ph )


  assert |- ( A. x ph -> ph )

  proof
    wph
    wph
    vx
    vy
    spnfw.1
    vx
    vy
    weq
    wph
    idd
    spimw
end
