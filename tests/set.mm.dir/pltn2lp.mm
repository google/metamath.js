include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "cple.mm"
include "cfv.mm"
include "eqid.mm"
include "pltnle.mm"
include "ex.mm"
include "pltle.mm"
include "3com23.mm"
include "nsyld.mm"
include "imnan.mm"
include "sylib.mm"

theorem pltn2lp
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let cX: class X
  let cY: class Y
  assume pltnlt.b: |- B = ( Base ` K )
  assume pltnlt.s: |- .< = ( lt ` K )


  assert |- ( ( K e. Poset /\ X e. B /\ Y e. B ) -> -. ( X .< Y /\ Y .< X ) )

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
    cY
    cX
    c.lt
    wbr
    #
    wn
    wi
    @4
    @5
    wa
    wn
    @3
    @4
    cY
    cX
    cK
    cple
    cfv
    #
    wbr
    #
    @5
    @3
    @4
    @7
    wn
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
    ex
    @0
    @2
    @1
    @5
    @7
    wi
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
    nsyld
    @4
    @5
    imnan
    sylib
end
