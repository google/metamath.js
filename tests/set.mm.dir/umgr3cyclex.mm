include "cumgr.mm"
include "wcel.mm"
include "w3a.mm"
include "cpr.mm"
include "cuhgr.mm"
include "wne.mm"
include "cv.mm"
include "ccycls.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "c3.mm"
include "wceq.mm"
include "cc0.mm"
include "wex.mm"
include "umgruhgr.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "wa.mm"
include "umgredgne.mm"
include "3ad2antr1.mm"
include "prcom.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "sylan2.mm"
include "3jca.mm"
include "3adant2.mm"
include "simp3.mm"
include "uhgr3cyclex.mm"
include "syl121anc.mm"

theorem umgr3cyclex
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let cE: class E
  let cG: class G
  let cV: class V
  let vp: setvar p
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  assume uhgr3cyclex.v: |- V = ( Vtx ` G )
  assume uhgr3cyclex.e: |- E = ( Edg ` G )

  disjoint A f
  disjoint A p
  disjoint f p
  disjoint B f
  disjoint B p
  disjoint C f
  disjoint C p
  disjoint G f
  disjoint G p
  disjoint A i
  disjoint A j
  disjoint A k
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint i j
  disjoint i k
  disjoint i p
  disjoint j k
  disjoint j p
  disjoint k p
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint C i
  disjoint C j
  disjoint C k
  disjoint G i
  disjoint G j
  disjoint G k
  disjoint V i
  disjoint V j
  disjoint V k
  assert |- ( ( G e. UMGraph /\ ( A e. V /\ B e. V /\ C e. V ) /\ ( { A , B } e. E /\ { B , C } e. E /\ { C , A } e. E ) ) -> E. f E. p ( f ( Cycles ` G ) p /\ ( # ` f ) = 3 /\ ( p ` 0 ) = A ) )

  proof
    cG
    cumgr
    wcel
    #
    cA
    cV
    wcel
    cB
    cV
    wcel
    cC
    cV
    wcel
    w3a
    #
    cA
    cB
    cpr
    cE
    wcel
    #
    cB
    cC
    cpr
    cE
    wcel
    #
    cC
    cA
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    w3a
    cG
    cuhgr
    wcel
    #
    @1
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    w3a
    #
    @6
    vf
    cv
    #
    vp
    cv
    #
    cG
    ccycls
    cfv
    wbr
    @12
    chash
    cfv
    c3
    wceq
    cc0
    @13
    cfv
    cA
    wceq
    w3a
    vp
    wex
    vf
    wex
    @0
    @1
    @7
    @6
    cG
    umgruhgr
    3ad2ant1
    @0
    @1
    @6
    simp2
    @0
    @6
    @11
    @1
    @0
    @6
    wa
    @8
    @9
    @10
    @0
    @3
    @2
    @8
    @5
    cE
    cG
    cA
    cB
    uhgr3cyclex.e
    umgredgne
    3ad2antr1
    @6
    @0
    cA
    cC
    cpr
    #
    cE
    wcel
    #
    @9
    @5
    @2
    @15
    @3
    @5
    @15
    @4
    @14
    cE
    cC
    cA
    prcom
    eleq1i
    biimpi
    3ad2ant3
    cE
    cG
    cA
    cC
    uhgr3cyclex.e
    umgredgne
    sylan2
    @6
    @0
    @3
    @10
    @2
    @3
    @5
    simp2
    cE
    cG
    cB
    cC
    uhgr3cyclex.e
    umgredgne
    sylan2
    3jca
    3adant2
    @0
    @1
    @6
    simp3
    cA
    cB
    cC
    vf
    cE
    cG
    cV
    vp
    uhgr3cyclex.v
    uhgr3cyclex.e
    uhgr3cyclex
    syl121anc
end
