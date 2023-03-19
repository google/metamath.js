include "cbs.mm"
include "cfv.mm"
include "c1.mm"
include "df-base.mm"
include "1nn.mm"
include "1lt5.mm"
include "zlmlem.mm"
include "eqtri.mm"

theorem zlmbas
  let cB: class B
  let cG: class G
  let cW: class W
  assume zlmbas.w: |- W = ( ZMod ` G )
  assume zlmbas.2: |- B = ( Base ` G )


  assert |- B = ( Base ` W )

  proof
    cB
    cG
    cbs
    cfv
    cW
    cbs
    cfv
    zlmbas.2
    cbs
    cG
    c1
    cW
    zlmbas.w
    df-base
    1nn
    1lt5
    zlmlem
    eqtri
end
