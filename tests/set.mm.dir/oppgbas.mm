include "cbs.mm"
include "cfv.mm"
include "c1.mm"
include "df-base.mm"
include "1nn.mm"
include "1ne2.mm"
include "oppglem.mm"
include "eqtri.mm"

theorem oppgbas
  let cB: class B
  let cR: class R
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume oppgbas.1: |- O = ( oppG ` R )
  assume oppgbas.2: |- B = ( Base ` R )


  assert |- B = ( Base ` O )

  proof
    cB
    cR
    cbs
    cfv
    cO
    cbs
    cfv
    oppgbas.2
    cR
    cbs
    c1
    cO
    oppgbas.1
    df-base
    1nn
    1ne2
    oppglem
    eqtri
end
