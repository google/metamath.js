include "cbs.mm"
include "cfv.mm"
include "c1.mm"
include "df-base.mm"
include "1nn.mm"
include "1ne2.mm"
include "mgplem.mm"
include "eqtri.mm"

theorem mgpbas
  let cB: class B
  let cR: class R
  let cM: class M
  assume mgpbas.1: |- M = ( mulGrp ` R )
  assume mgpbas.2: |- B = ( Base ` R )


  assert |- B = ( Base ` M )

  proof
    cB
    cR
    cbs
    cfv
    cM
    cbs
    cfv
    mgpbas.2
    cR
    cbs
    cM
    c1
    mgpbas.1
    df-base
    1nn
    1ne2
    mgplem
    eqtri
end
