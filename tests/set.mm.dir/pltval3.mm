include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wne.mm"
include "wa.mm"
include "wn.mm"
include "pltval.mm"
include "wceq.mm"
include "wi.mm"
include "posref.mm"
include "3adant3.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "adantr.mm"
include "posasymb.mm"
include "biimpd.mm"
include "expdimp.mm"
include "impbid.mm"
include "necon3abid.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem pltval3
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume pleval2.b: |- B = ( Base ` K )
  assume pleval2.l: |- .<_ = ( le ` K )
  assume pleval2.s: |- .< = ( lt ` K )


  assert |- ( ( K e. Poset /\ X e. B /\ Y e. B ) -> ( X .< Y <-> ( X .<_ Y /\ -. Y .<_ X ) ) )

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
    cX
    cY
    c.le
    wbr
    #
    cX
    cY
    wne
    #
    wa
    @4
    cY
    cX
    c.le
    wbr
    #
    wn
    #
    wa
    cpo
    cB
    cB
    c.lt
    cK
    c.le
    cX
    cY
    pleval2.l
    pleval2.s
    pltval
    @3
    @4
    @5
    @7
    @3
    @4
    wa
    #
    @6
    cX
    cY
    @8
    cX
    cY
    wceq
    #
    @6
    @3
    @9
    @6
    wi
    @4
    @3
    cX
    cX
    c.le
    wbr
    #
    @9
    @6
    @0
    @1
    @10
    @2
    cB
    cK
    c.le
    cX
    pleval2.b
    pleval2.l
    posref
    3adant3
    cX
    cY
    cX
    c.le
    breq1
    syl5ibcom
    adantr
    @3
    @4
    @6
    @9
    @3
    @4
    @6
    wa
    @9
    cB
    cK
    c.le
    cX
    cY
    pleval2.b
    pleval2.l
    posasymb
    biimpd
    expdimp
    impbid
    necon3abid
    pm5.32da
    bitrd
end
