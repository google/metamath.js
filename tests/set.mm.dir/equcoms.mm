include "weq.mm"
include "equcomi.mm"
include "syl.mm"

theorem equcoms
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y
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
