include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wb.mm"
include "pleval2.mm"
include "3adant3r3.mm"
include "plttr.mm"
include "expd.mm"
include "breq1.mm"
include "biimprd.mm"
include "a1i.mm"
include "jaod.mm"
include "sylbid.mm"
include "impd.mm"

theorem plelttr
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume pltletr.b: |- B = ( Base ` K )
  assume pltletr.l: |- .<_ = ( le ` K )
  assume pltletr.s: |- .< = ( lt ` K )


  assert |- ( ( K e. Poset /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .<_ Y /\ Y .< Z ) -> X .< Z ) )

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
    cZ
    cB
    wcel
    #
    w3a
    wa
    #
    cX
    cY
    c.le
    wbr
    #
    cY
    cZ
    c.lt
    wbr
    #
    cX
    cZ
    c.lt
    wbr
    #
    @4
    @5
    cX
    cY
    c.lt
    wbr
    #
    cX
    cY
    wceq
    #
    wo
    #
    @6
    @7
    wi
    #
    @0
    @1
    @2
    @5
    @10
    wb
    @3
    cB
    c.lt
    cK
    c.le
    cX
    cY
    pltletr.b
    pltletr.l
    pltletr.s
    pleval2
    3adant3r3
    @4
    @8
    @11
    @9
    @4
    @8
    @6
    @7
    cB
    c.lt
    cK
    cX
    cY
    cZ
    pltletr.b
    pltletr.s
    plttr
    expd
    @9
    @11
    wi
    @4
    @9
    @7
    @6
    cX
    cY
    cZ
    c.lt
    breq1
    biimprd
    a1i
    jaod
    sylbid
    impd
end
