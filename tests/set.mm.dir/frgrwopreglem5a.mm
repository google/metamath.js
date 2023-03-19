include "cfrgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wne.mm"
include "w3a.mm"
include "cpr.mm"
include "id.mm"
include "simpl.mm"
include "anim12i.mm"
include "simp2.mm"
include "frgrwopreglem4a.mm"
include "syl3an.mm"
include "simpr.mm"
include "anim12ci.mm"
include "pm13.18.mm"
include "3adant3.mm"
include "necomd.mm"
include "simp3.mm"
include "pm13.181.mm"
include "3adant2.mm"
include "jca.mm"
include "jca31.mm"

theorem frgrwopreglem5a
  let cA: class A
  let cB: class B
  let cD: class D
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  assume frgrncvvdeq.v: |- V = ( Vtx ` G )
  assume frgrncvvdeq.d: |- D = ( VtxDeg ` G )
  assume frgrwopreglem4a.e: |- E = ( Edg ` G )


  assert |- ( ( G e. FriendGraph /\ ( ( A e. V /\ X e. V ) /\ ( B e. V /\ Y e. V ) ) /\ ( ( D ` A ) = ( D ` X ) /\ ( D ` A ) =/= ( D ` B ) /\ ( D ` X ) =/= ( D ` Y ) ) ) -> ( ( { A , B } e. E /\ { B , X } e. E ) /\ ( { X , Y } e. E /\ { Y , A } e. E ) ) )

  proof
    cG
    cfrgr
    wcel
    #
    cA
    cV
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    cB
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    wa
    #
    cA
    cD
    cfv
    #
    cX
    cD
    cfv
    #
    wceq
    #
    @8
    cB
    cD
    cfv
    #
    wne
    #
    @9
    cY
    cD
    cfv
    #
    wne
    #
    w3a
    #
    w3a
    #
    cA
    cB
    cpr
    cE
    wcel
    #
    cB
    cX
    cpr
    cE
    wcel
    #
    cX
    cY
    cpr
    cE
    wcel
    #
    cY
    cA
    cpr
    cE
    wcel
    #
    wa
    @0
    @0
    @7
    @1
    @4
    wa
    @15
    @12
    @17
    @0
    id
    #
    @3
    @1
    @6
    @4
    @1
    @2
    simpl
    #
    @4
    @5
    simpl
    #
    anim12i
    @10
    @12
    @14
    simp2
    cD
    cE
    cG
    cV
    cA
    cB
    frgrncvvdeq.v
    frgrncvvdeq.d
    frgrwopreglem4a.e
    frgrwopreglem4a
    syl3an
    @0
    @0
    @7
    @4
    @2
    wa
    @15
    @11
    @9
    wne
    @18
    @21
    @3
    @2
    @6
    @4
    @1
    @2
    simpr
    #
    @23
    anim12ci
    @15
    @9
    @11
    @10
    @12
    @9
    @11
    wne
    @14
    @8
    @9
    @11
    pm13.18
    3adant3
    necomd
    cD
    cE
    cG
    cV
    cB
    cX
    frgrncvvdeq.v
    frgrncvvdeq.d
    frgrwopreglem4a.e
    frgrwopreglem4a
    syl3an
    @16
    @19
    @20
    @0
    @0
    @7
    @2
    @5
    wa
    @15
    @14
    @19
    @21
    @3
    @2
    @6
    @5
    @24
    @4
    @5
    simpr
    #
    anim12i
    @10
    @12
    @14
    simp3
    cD
    cE
    cG
    cV
    cX
    cY
    frgrncvvdeq.v
    frgrncvvdeq.d
    frgrwopreglem4a.e
    frgrwopreglem4a
    syl3an
    @0
    @0
    @7
    @5
    @1
    wa
    @15
    @13
    @8
    wne
    @20
    @21
    @3
    @1
    @6
    @5
    @22
    @25
    anim12ci
    @15
    @8
    @13
    @10
    @14
    @8
    @13
    wne
    @12
    @8
    @9
    @13
    pm13.181
    3adant2
    necomd
    cD
    cE
    cG
    cV
    cY
    cA
    frgrncvvdeq.v
    frgrncvvdeq.d
    frgrwopreglem4a.e
    frgrwopreglem4a
    syl3an
    jca
    jca31
end
