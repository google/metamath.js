include "cbs.mm"
include "cfv.mm"
include "c1.mm"
include "df-base.mm"
include "1nn.mm"
include "1lt3.mm"
include "opprlem.mm"
include "eqtri.mm"

theorem opprbas
  let cB: class B
  let cR: class R
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume opprbas.1: |- O = ( oppR ` R )
  assume opprbas.2: |- B = ( Base ` R )


  assert |- B = ( Base ` O )

  proof
    cB
    cR
    cbs
    cfv
    cO
    cbs
    cfv
    opprbas.2
    cR
    cbs
    c1
    cO
    opprbas.1
    df-base
    1nn
    1lt3
    opprlem
    eqtri
end
