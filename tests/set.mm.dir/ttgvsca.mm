include "cvsca.mm"
include "cfv.mm"
include "c6.mm"
include "df-vsca.mm"
include "6nn.mm"
include "c1.mm"
include "1nn.mm"
include "6nn0.mm"
include "6lt10.mm"
include "declti.mm"
include "ttglem.mm"
include "eqtri.mm"

theorem ttgvsca
  let c.x: class .x.
  let cG: class G
  let cH: class H
  assume ttgval.n: |- G = ( toTG ` H )
  assume ttgvsca.1: |- .x. = ( .s ` H )


  assert |- .x. = ( .s ` G )

  proof
    c.x
    cH
    cvsca
    cfv
    cG
    cvsca
    cfv
    ttgvsca.1
    cvsca
    cG
    cH
    c6
    ttgval.n
    df-vsca
    6nn
    c1
    c6
    c6
    1nn
    6nn0
    6nn0
    6lt10
    declti
    ttglem
    eqtri
end
