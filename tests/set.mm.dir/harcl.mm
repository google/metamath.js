include "cvv.mm"
include "con0.mm"
include "char.mm"
include "harf.mm"
include "0elon.mm"
include "f0cli.mm"

theorem harcl
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cY: class Y


  assert |- ( har ` X ) e. On

  proof
    cvv
    con0
    cX
    char
    harf
    0elon
    f0cli
end
