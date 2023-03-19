include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cfv.mm"
include "wa.mm"
include "simpl1.mm"
include "simpl3.mm"
include "simpr.mm"
include "polcon2N.mm"
include "syl3anc.mm"
include "simpl2.mm"
include "impbida.mm"

theorem polcon2bN
  let cA: class A
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume 2polss.a: |- A = ( Atoms ` K )
  assume 2polss.p: |- ._|_ = ( _|_P ` K )


  assert |- ( ( K e. HL /\ X C_ A /\ Y C_ A ) -> ( X C_ ( ._|_ ` Y ) <-> Y C_ ( ._|_ ` X ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    #
    cY
    cA
    wss
    #
    w3a
    #
    cX
    cY
    c.pe
    cfv
    wss
    #
    cY
    cX
    c.pe
    cfv
    wss
    #
    @3
    @4
    wa
    @0
    @2
    @4
    @5
    @0
    @1
    @2
    @4
    simpl1
    @0
    @1
    @2
    @4
    simpl3
    @3
    @4
    simpr
    cA
    cK
    c.pe
    cX
    cY
    2polss.a
    2polss.p
    polcon2N
    syl3anc
    @3
    @5
    wa
    @0
    @1
    @5
    @4
    @0
    @1
    @2
    @5
    simpl1
    @0
    @1
    @2
    @5
    simpl2
    @3
    @5
    simpr
    cA
    cK
    c.pe
    cY
    cX
    2polss.a
    2polss.p
    polcon2N
    syl3anc
    impbida
end
