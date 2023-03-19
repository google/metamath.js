include "cops.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cple.mm"
include "cfv.mm"
include "wne.mm"
include "wb.mm"
include "simpl.mm"
include "op0cl.mm"
include "adantr.mm"
include "simpr.mm"
include "eqid.mm"
include "pltval.mm"
include "syl3anc.mm"
include "necom.mm"
include "op0le.mm"
include "biantrurd.mm"
include "syl5rbb.mm"
include "bitrd.mm"

theorem opltn0
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let cX: class X
  let c.0: class .0.
  assume opltne0.b: |- B = ( Base ` K )
  assume opltne0.s: |- .< = ( lt ` K )
  assume opltne0.z: |- .0. = ( 0. ` K )


  assert |- ( ( K e. OP /\ X e. B ) -> ( .0. .< X <-> X =/= .0. ) )

  proof
    cK
    cops
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    c.0
    cX
    c.lt
    wbr
    #
    c.0
    cX
    cK
    cple
    cfv
    #
    wbr
    #
    c.0
    cX
    wne
    #
    wa
    #
    cX
    c.0
    wne
    #
    @2
    @0
    c.0
    cB
    wcel
    #
    @1
    @3
    @7
    wb
    @0
    @1
    simpl
    @0
    @9
    @1
    cB
    cK
    c.0
    opltne0.b
    opltne0.z
    op0cl
    adantr
    @0
    @1
    simpr
    cops
    cB
    cB
    c.lt
    cK
    @4
    c.0
    cX
    @4
    eqid
    #
    opltne0.s
    pltval
    syl3anc
    @8
    @6
    @2
    @7
    cX
    c.0
    necom
    @2
    @5
    @6
    cB
    cK
    @4
    cX
    c.0
    opltne0.b
    @10
    opltne0.z
    op0le
    biantrurd
    syl5rbb
    bitrd
end
