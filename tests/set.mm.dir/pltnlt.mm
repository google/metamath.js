include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "cple.mm"
include "cfv.mm"
include "eqid.mm"
include "pltnle.mm"
include "wi.mm"
include "pltle.mm"
include "3com23.mm"
include "adantr.mm"
include "mtod.mm"

theorem pltnlt
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let cX: class X
  let cY: class Y
  assume pltnlt.b: |- B = ( Base ` K )
  assume pltnlt.s: |- .< = ( lt ` K )


  assert |- ( ( ( K e. Poset /\ X e. B /\ Y e. B ) /\ X .< Y ) -> -. Y .< X )

  proof
    cK
    cpo
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
    c.lt
    wbr
    #
    wa
    cY
    cX
    c.lt
    wbr
    #
    cY
    cX
    cK
    cple
    cfv
    #
    wbr
    #
    cB
    c.lt
    cK
    @6
    cX
    cY
    pltnlt.b
    @6
    eqid
    #
    pltnlt.s
    pltnle
    @3
    @5
    @7
    wi
    #
    @4
    @0
    @2
    @1
    @9
    cpo
    cB
    cB
    c.lt
    cK
    @6
    cY
    cX
    @8
    pltnlt.s
    pltle
    3com23
    adantr
    mtod
end
