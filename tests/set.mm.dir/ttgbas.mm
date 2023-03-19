include "cbs.mm"
include "cfv.mm"
include "c1.mm"
include "df-base.mm"
include "1nn.mm"
include "c6.mm"
include "6nn0.mm"
include "1nn0.mm"
include "1lt10.mm"
include "declti.mm"
include "ttglem.mm"
include "eqtri.mm"

theorem ttgbas
  let cB: class B
  let cG: class G
  let cH: class H
  assume ttgval.n: |- G = ( toTG ` H )
  assume ttgbas.1: |- B = ( Base ` H )


  assert |- B = ( Base ` G )

  proof
    cB
    cH
    cbs
    cfv
    cG
    cbs
    cfv
    ttgbas.1
    cbs
    cG
    cH
    c1
    ttgval.n
    df-base
    1nn
    c1
    c6
    c1
    1nn
    6nn0
    1nn0
    1lt10
    declti
    ttglem
    eqtri
end
