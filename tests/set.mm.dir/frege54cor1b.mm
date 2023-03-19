include "equsb1.mm"

theorem frege54cor1b
  let vx: setvar x
  let vy: setvar y


  assert |- [ x / y ] y = x

  proof
    vy
    vx
    equsb1
end
