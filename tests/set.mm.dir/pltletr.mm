include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "pleval2.mm"
include "3adant3r1.mm"
include "adantr.mm"
include "plttr.mm"
include "expdimp.mm"
include "wi.mm"
include "breq2.mm"
include "biimpcd.mm"
include "adantl.mm"
include "jaod.mm"
include "sylbid.mm"
include "expimpd.mm"

theorem pltletr
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


  assert |- ( ( K e. Poset /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .< Y /\ Y .<_ Z ) -> X .< Z ) )

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
    c.lt
    wbr
    #
    cY
    cZ
    c.le
    wbr
    #
    cX
    cZ
    c.lt
    wbr
    #
    @4
    @5
    wa
    #
    @6
    cY
    cZ
    c.lt
    wbr
    #
    cY
    cZ
    wceq
    #
    wo
    #
    @7
    @4
    @6
    @11
    wb
    #
    @5
    @0
    @2
    @3
    @12
    @1
    cB
    c.lt
    cK
    c.le
    cY
    cZ
    pltletr.b
    pltletr.l
    pltletr.s
    pleval2
    3adant3r1
    adantr
    @8
    @9
    @7
    @10
    @4
    @5
    @9
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
    expdimp
    @5
    @10
    @7
    wi
    @4
    @10
    @5
    @7
    cY
    cZ
    cX
    c.lt
    breq2
    biimpcd
    adantl
    jaod
    sylbid
    expimpd
end
