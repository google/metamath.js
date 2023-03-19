include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cfv.mm"
include "wa.mm"
include "simpl1.mm"
include "simp1.mm"
include "polssatN.mm"
include "3adant2.mm"
include "syl2anc.mm"
include "adantr.mm"
include "simpr.mm"
include "polcon3N.mm"
include "syl3anc.mm"
include "ex.mm"
include "wceq.mm"
include "3polN.mm"
include "3adant3.mm"
include "sseq12d.mm"
include "sylibd.mm"
include "impbid.mm"

theorem 2polcon4bN
  let cA: class A
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume 2polss.a: |- A = ( Atoms ` K )
  assume 2polss.p: |- ._|_ = ( _|_P ` K )


  assert |- ( ( K e. HL /\ X C_ A /\ Y C_ A ) -> ( ( ._|_ ` ( ._|_ ` X ) ) C_ ( ._|_ ` ( ._|_ ` Y ) ) <-> ( ._|_ ` Y ) C_ ( ._|_ ` X ) ) )

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
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cY
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    wss
    #
    @6
    @4
    wss
    #
    @3
    @8
    @7
    c.pe
    cfv
    #
    @5
    c.pe
    cfv
    #
    wss
    #
    @9
    @3
    @8
    @12
    @3
    @8
    wa
    @0
    @7
    cA
    wss
    #
    @8
    @12
    @0
    @1
    @2
    @8
    simpl1
    @3
    @13
    @8
    @3
    @0
    @6
    cA
    wss
    #
    @13
    @0
    @1
    @2
    simp1
    @0
    @2
    @14
    @1
    cA
    cK
    c.pe
    cY
    2polss.a
    2polss.p
    polssatN
    3adant2
    cA
    cK
    c.pe
    @6
    2polss.a
    2polss.p
    polssatN
    syl2anc
    adantr
    @3
    @8
    simpr
    cA
    cK
    c.pe
    @5
    @7
    2polss.a
    2polss.p
    polcon3N
    syl3anc
    ex
    @3
    @10
    @6
    @11
    @4
    @0
    @2
    @10
    @6
    wceq
    @1
    cA
    cY
    cK
    c.pe
    2polss.a
    2polss.p
    3polN
    3adant2
    @0
    @1
    @11
    @4
    wceq
    @2
    cA
    cX
    cK
    c.pe
    2polss.a
    2polss.p
    3polN
    3adant3
    sseq12d
    sylibd
    @3
    @9
    @8
    @3
    @9
    wa
    @0
    @4
    cA
    wss
    #
    @9
    @8
    @0
    @1
    @2
    @9
    simpl1
    @3
    @15
    @9
    @0
    @1
    @15
    @2
    cA
    cK
    c.pe
    cX
    2polss.a
    2polss.p
    polssatN
    3adant3
    adantr
    @3
    @9
    simpr
    cA
    cK
    c.pe
    @6
    @4
    2polss.a
    2polss.p
    polcon3N
    syl3anc
    ex
    impbid
end
