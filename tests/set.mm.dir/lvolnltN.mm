include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "pltirr.mm"
include "3adant3.mm"
include "breq2.mm"
include "notbid.mm"
include "syl5ibcom.mm"
include "cple.mm"
include "cfv.mm"
include "eqid.mm"
include "pltle.mm"
include "lvolcmp.mm"
include "sylibd.mm"
include "necon3ad.mm"
include "pm2.61dne.mm"

theorem lvolnltN
  let c.lt: class .<
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  assume lvolnlt.s: |- .< = ( lt ` K )
  assume lvolnlt.v: |- V = ( LVols ` K )


  assert |- ( ( K e. HL /\ X e. V /\ Y e. V ) -> -. X .< Y )

  proof
    cK
    chlt
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    w3a
    #
    cX
    cY
    c.lt
    wbr
    #
    wn
    #
    cX
    cY
    @3
    cX
    cX
    c.lt
    wbr
    #
    wn
    #
    cX
    cY
    wceq
    #
    @5
    @0
    @1
    @7
    @2
    chlt
    cV
    c.lt
    cK
    cX
    lvolnlt.s
    pltirr
    3adant3
    @8
    @6
    @4
    cX
    cY
    cX
    c.lt
    breq2
    notbid
    syl5ibcom
    @3
    @4
    cX
    cY
    @3
    @4
    cX
    cY
    cK
    cple
    cfv
    #
    wbr
    @8
    chlt
    cV
    cV
    c.lt
    cK
    @9
    cX
    cY
    @9
    eqid
    #
    lvolnlt.s
    pltle
    cK
    @9
    cV
    cX
    cY
    @10
    lvolnlt.v
    lvolcmp
    sylibd
    necon3ad
    pm2.61dne
end
