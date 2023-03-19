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
include "llncmp.mm"
include "sylibd.mm"
include "necon3ad.mm"
include "pm2.61dne.mm"

theorem llnnlt
  let c.lt: class .<
  let cK: class K
  let cN: class N
  let cX: class X
  let cY: class Y
  assume llnnlt.s: |- .< = ( lt ` K )
  assume llnnlt.n: |- N = ( LLines ` K )


  assert |- ( ( K e. HL /\ X e. N /\ Y e. N ) -> -. X .< Y )

  proof
    cK
    chlt
    wcel
    #
    cX
    cN
    wcel
    #
    cY
    cN
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
    cN
    c.lt
    cK
    cX
    llnnlt.s
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
    cN
    cN
    c.lt
    cK
    @9
    cX
    cY
    @9
    eqid
    #
    llnnlt.s
    pltle
    cK
    @9
    cN
    cX
    cY
    @10
    llnnlt.n
    llncmp
    sylibd
    necon3ad
    pm2.61dne
end
