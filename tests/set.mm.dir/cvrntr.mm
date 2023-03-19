include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "cplt.mm"
include "cfv.mm"
include "wn.mm"
include "wi.mm"
include "eqid.mm"
include "cvrlt.mm"
include "ex.mm"
include "3adant3r3.mm"
include "ltcvrntr.mm"
include "syland.mm"

theorem cvrntr
  let cA: class A
  let cB: class B
  let cC: class C
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume cvrntr.b: |- B = ( Base ` K )
  assume cvrntr.c: |- C = ( <o ` K )


  assert |- ( ( K e. A /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X C Y /\ Y C Z ) -> -. X C Z ) )

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
    cX
    cY
    cC
    wbr
    #
    cX
    cY
    cK
    cplt
    cfv
    #
    wbr
    #
    cY
    cZ
    cC
    wbr
    cX
    cZ
    cC
    wbr
    wn
    @0
    @1
    @2
    @4
    @6
    wi
    @3
    @0
    @1
    @2
    w3a
    @4
    @6
    cA
    cB
    cC
    @5
    cK
    cX
    cY
    cvrntr.b
    @5
    eqid
    #
    cvrntr.c
    cvrlt
    ex
    3adant3r3
    cA
    cB
    cC
    @5
    cK
    cX
    cY
    cZ
    cvrntr.b
    @7
    cvrntr.c
    ltcvrntr
    syland
end
