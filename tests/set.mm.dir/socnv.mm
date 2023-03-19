include "wor.mm"
include "ccnv.mm"
include "cnvso.mm"
include "biimpi.mm"

theorem socnv
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R Or A -> `' R Or A )

  proof
    cA
    cR
    wor
    cA
    cR
    ccnv
    wor
    cA
    cR
    cnvso
    biimpi
end
