include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "pleval2i.mm"
include "3adant1.mm"
include "pltle.mm"
include "posref.mm"
include "3adant3.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "jaod.mm"
include "impbid.mm"

theorem pleval2
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume pleval2.b: |- B = ( Base ` K )
  assume pleval2.l: |- .<_ = ( le ` K )
  assume pleval2.s: |- .< = ( lt ` K )


  assert |- ( ( K e. Poset /\ X e. B /\ Y e. B ) -> ( X .<_ Y <-> ( X .< Y \/ X = Y ) ) )

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
    c.le
    wbr
    #
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
    @1
    @2
    @4
    @7
    wi
    @0
    cB
    c.lt
    cK
    c.le
    cX
    cY
    pleval2.b
    pleval2.l
    pleval2.s
    pleval2i
    3adant1
    @3
    @5
    @4
    @6
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
    pltle
    @3
    cX
    cX
    c.le
    wbr
    #
    @6
    @4
    @0
    @1
    @8
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
    breq2
    syl5ibcom
    jaod
    impbid
end
