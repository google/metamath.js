include "weq.mm"
include "equcomi.mm"
include "syl.mm"

theorem equcoms
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume equcoms.1: |- ( x = y -> ph )


  assert |- ( y = x -> ph )

  proof
    vy
    vx
    weq
    vx
    vy
    weq
    wph
    vy
    vx
    equcomi
    equcoms.1
    syl
end
