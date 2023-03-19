include "cabl.mm"
include "wcel.mm"
include "ccmn.mm"
include "co.mm"
include "wceq.mm"
include "ablcmn.mm"
include "cmncom.mm"
include "syl3an1.mm"

theorem ablcom
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let cW: class W
  let cZ: class Z
  assume ablcom.b: |- B = ( Base ` G )
  assume ablcom.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Abel /\ X e. B /\ Y e. B ) -> ( X .+ Y ) = ( Y .+ X ) )

  proof
    cG
    cabl
    wcel
    cG
    ccmn
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    cX
    cY
    c.pl
    co
    cY
    cX
    c.pl
    co
    wceq
    cG
    ablcmn
    cB
    c.pl
    cG
    cX
    cY
    ablcom.b
    ablcom.p
    cmncom
    syl3an1
end
