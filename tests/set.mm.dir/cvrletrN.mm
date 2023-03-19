include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "simpll.mm"
include "simplr1.mm"
include "simplr2.mm"
include "simpr.mm"
include "cvrlt.mm"
include "syl31anc.mm"
include "wi.mm"
include "pltletr.mm"
include "adantr.mm"
include "mpand.mm"
include "expimpd.mm"

theorem cvrletrN
  let cB: class B
  let cC: class C
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume cvrletr.b: |- B = ( Base ` K )
  assume cvrletr.l: |- .<_ = ( le ` K )
  assume cvrletr.s: |- .< = ( lt ` K )
  assume cvrletr.c: |- C = ( <o ` K )


  assert |- ( ( K e. Poset /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X C Y /\ Y .<_ Z ) -> X .< Z ) )

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
    #
    wa
    #
    cX
    cY
    cC
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
    @5
    @6
    wa
    #
    cX
    cY
    c.lt
    wbr
    #
    @7
    @8
    @9
    @0
    @1
    @2
    @6
    @10
    @0
    @4
    @6
    simpll
    @1
    @2
    @3
    @0
    @6
    simplr1
    @1
    @2
    @3
    @0
    @6
    simplr2
    @5
    @6
    simpr
    cpo
    cB
    cC
    c.lt
    cK
    cX
    cY
    cvrletr.b
    cvrletr.s
    cvrletr.c
    cvrlt
    syl31anc
    @5
    @10
    @7
    wa
    @8
    wi
    @6
    cB
    c.lt
    cK
    c.le
    cX
    cY
    cZ
    cvrletr.b
    cvrletr.l
    cvrletr.s
    pltletr
    adantr
    mpand
    expimpd
end
