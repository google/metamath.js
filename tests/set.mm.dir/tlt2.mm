include "ctos.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wo.mm"
include "wn.mm"
include "exmidd.mm"
include "wb.mm"
include "tltnle.mm"
include "3com23.mm"
include "orbi2d.mm"
include "mpbird.mm"

theorem tlt2
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume tlt2.b: |- B = ( Base ` K )
  assume tlt2.e: |- .<_ = ( le ` K )
  assume tlt2.l: |- .< = ( lt ` K )


  assert |- ( ( K e. Toset /\ X e. B /\ Y e. B ) -> ( X .<_ Y \/ Y .< X ) )

  proof
    cK
    ctos
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.le
    wbr
    #
    cY
    cX
    c.lt
    wbr
    #
    wo
    @4
    @4
    wn
    #
    wo
    @3
    @4
    exmidd
    @3
    @5
    @6
    @4
    @0
    @2
    @1
    @5
    @6
    wb
    cB
    c.lt
    cK
    c.le
    cY
    cX
    tlt2.b
    tlt2.e
    tlt2.l
    tltnle
    3com23
    orbi2d
    mpbird
end
