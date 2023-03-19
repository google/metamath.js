include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "cvrlt.mm"
include "ex.mm"
include "3adant3r1.mm"
include "ltltncvr.mm"
include "sylan2d.mm"

theorem ltcvrntr
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


  assert |- ( ( K e. A /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .< Y /\ Y C Z ) -> -. X C Z ) )

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
    wa
    cY
    cZ
    cC
    wbr
    #
    cY
    cZ
    c.lt
    wbr
    #
    cX
    cY
    c.lt
    wbr
    cX
    cZ
    cC
    wbr
    wn
    @0
    @2
    @3
    @4
    @5
    wi
    @1
    @0
    @2
    @3
    w3a
    @4
    @5
    cA
    cB
    cC
    c.lt
    cK
    cY
    cZ
    ltltncvr.b
    ltltncvr.s
    ltltncvr.c
    cvrlt
    ex
    3adant3r1
    cA
    cB
    cC
    c.lt
    cK
    cX
    cY
    cZ
    ltltncvr.b
    ltltncvr.s
    ltltncvr.c
    ltltncvr
    sylan2d
end
