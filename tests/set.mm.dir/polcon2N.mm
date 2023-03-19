include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "cfv.mm"
include "w3a.mm"
include "2polssN.mm"
include "3adant3.mm"
include "polssatN.mm"
include "polcon3N.mm"
include "syld3an2.mm"
include "sstrd.mm"

theorem polcon2N
  let cA: class A
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume 2polss.a: |- A = ( Atoms ` K )
  assume 2polss.p: |- ._|_ = ( _|_P ` K )


  assert |- ( ( K e. HL /\ Y C_ A /\ X C_ ( ._|_ ` Y ) ) -> Y C_ ( ._|_ ` X ) )

  proof
    cK
    chlt
    wcel
    #
    cY
    cA
    wss
    #
    cX
    cY
    c.pe
    cfv
    #
    wss
    #
    w3a
    cY
    @2
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
    @0
    @1
    cY
    @4
    wss
    @3
    cA
    cK
    c.pe
    cY
    2polss.a
    2polss.p
    2polssN
    3adant3
    @0
    @2
    cA
    wss
    #
    @1
    @3
    @4
    @5
    wss
    @0
    @1
    @6
    @3
    cA
    cK
    c.pe
    cY
    2polss.a
    2polss.p
    polssatN
    3adant3
    cA
    cK
    c.pe
    cX
    @2
    2polss.a
    2polss.p
    polcon3N
    syld3an2
    sstrd
end
