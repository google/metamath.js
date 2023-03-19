include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "simpll.mm"
include "simplr1.mm"
include "simplr3.mm"
include "simplr2.mm"
include "simpr.mm"
include "cvrnbtwn.mm"
include "syl131anc.mm"
include "ex.mm"
include "con2d.mm"

theorem ltltncvr
  let cA: class A
  let cB: class B
  let cC: class C
  let c.lt: class .<
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume ltltncvr.b: |- B = ( Base ` K )
  assume ltltncvr.s: |- .< = ( lt ` K )
  assume ltltncvr.c: |- C = ( <o ` K )


  assert |- ( ( K e. A /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .< Y /\ Y .< Z ) -> -. X C Z ) )

  proof
    cK
    cA
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
    cZ
    cC
    wbr
    #
    cX
    cY
    c.lt
    wbr
    cY
    cZ
    c.lt
    wbr
    wa
    #
    @5
    @6
    @7
    wn
    #
    @5
    @6
    wa
    @0
    @1
    @3
    @2
    @6
    @8
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
    simplr3
    @1
    @2
    @3
    @0
    @6
    simplr2
    @5
    @6
    simpr
    cA
    cB
    cC
    c.lt
    cK
    cX
    cZ
    cY
    ltltncvr.b
    ltltncvr.s
    ltltncvr.c
    cvrnbtwn
    syl131anc
    ex
    con2d
end
