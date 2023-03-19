include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "cfv.mm"
include "w3a.mm"
include "wceq.mm"
include "wa.mm"
include "cin.mm"
include "simp1.mm"
include "simp3.mm"
include "polssatN.mm"
include "3adant3.mm"
include "sstrd.mm"
include "3jca.mm"
include "3polN.mm"
include "jca.mm"
include "poml4N.mm"
include "sylc.mm"

theorem poml5N
  let cA: class A
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume poml4.a: |- A = ( Atoms ` K )
  assume poml4.p: |- ._|_ = ( _|_P ` K )


  assert |- ( ( K e. HL /\ Y C_ A /\ X C_ ( ._|_ ` Y ) ) -> ( ( ._|_ ` ( ( ._|_ ` X ) i^i ( ._|_ ` Y ) ) ) i^i ( ._|_ ` Y ) ) = ( ._|_ ` ( ._|_ ` X ) ) )

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
    #
    @0
    cX
    cA
    wss
    #
    @2
    cA
    wss
    #
    w3a
    @3
    @2
    c.pe
    cfv
    c.pe
    cfv
    @2
    wceq
    #
    wa
    cX
    c.pe
    cfv
    #
    @2
    cin
    c.pe
    cfv
    @2
    cin
    @8
    c.pe
    cfv
    wceq
    @4
    @0
    @5
    @6
    @0
    @1
    @3
    simp1
    @4
    cX
    @2
    cA
    @0
    @1
    @3
    simp3
    #
    @0
    @1
    @6
    @3
    cA
    cK
    c.pe
    cY
    poml4.a
    poml4.p
    polssatN
    3adant3
    #
    sstrd
    @10
    3jca
    @4
    @3
    @7
    @9
    @0
    @1
    @7
    @3
    cA
    cY
    cK
    c.pe
    poml4.a
    poml4.p
    3polN
    3adant3
    jca
    cA
    cK
    c.pe
    cX
    @2
    poml4.a
    poml4.p
    poml4N
    sylc
end
