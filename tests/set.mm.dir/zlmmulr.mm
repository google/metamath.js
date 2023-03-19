include "cmulr.mm"
include "cfv.mm"
include "c3.mm"
include "df-mulr.mm"
include "3nn.mm"
include "3lt5.mm"
include "zlmlem.mm"
include "eqtri.mm"

theorem zlmmulr
  let c.x: class .x.
  let cG: class G
  let cW: class W
  assume zlmbas.w: |- W = ( ZMod ` G )
  assume zlmmulr.2: |- .x. = ( .r ` G )


  assert |- .x. = ( .r ` W )

  proof
    c.x
    cG
    cmulr
    cfv
    cW
    cmulr
    cfv
    zlmmulr.2
    cmulr
    cG
    c3
    cW
    zlmbas.w
    df-mulr
    3nn
    3lt5
    zlmlem
    eqtri
end
