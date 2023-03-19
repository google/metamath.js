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
include "lplncmp.mm"
include "sylibd.mm"
include "necon3ad.mm"
include "pm2.61dne.mm"

theorem lplnnlt
  let cP: class P
  let c.lt: class .<
  let cK: class K
  let cX: class X
  let cY: class Y
  assume lplnnlt.s: |- .< = ( lt ` K )
  assume lplnnlt.p: |- P = ( LPlanes ` K )


  assert |- ( ( K e. HL /\ X e. P /\ Y e. P ) -> -. X .< Y )

  proof
    cK
    chlt
    wcel
    #
    cX
    cP
    wcel
    #
    cY
    cP
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
    cP
    c.lt
    cK
    cX
    lplnnlt.s
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
    cP
    cP
    c.lt
    cK
    @9
    cX
    cY
    @9
    eqid
    #
    lplnnlt.s
    pltle
    cP
    cK
    @9
    cX
    cY
    @10
    lplnnlt.p
    lplncmp
    sylibd
    necon3ad
    pm2.61dne
end
