include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "c-bnj14.mm"
include "c-bnj18.mm"
include "cv.mm"
include "ciun.mm"
include "cun.mm"
include "cvv.mm"
include "bnj1148.mm"
include "wral.mm"
include "bnj893.mm"
include "w3a.mm"
include "simp1.mm"
include "bnj1127.mm"
include "3ad2ant3.mm"
include "syl2anc.mm"
include "3expia.mm"
include "ralrimiv.mm"
include "iunexg.mm"
include "bnj1149.mm"
include "wss.mm"
include "bnj906.mm"
include "iunss1.mm"
include "unss2.mm"
include "3syl.mm"
include "syl5eqss.mm"
include "ssexd.mm"

theorem bnj1413
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  assume bnj1413.1: |- B = ( _pred ( X , A , R ) u. U_ y e. _pred ( X , A , R ) _trCl ( y , A , R ) )

  disjoint A y
  disjoint R y
  disjoint X y
  assert |- ( ( R _FrSe A /\ X e. A ) -> B e. _V )

  proof
    cA
    cR
    w-bnj15
    #
    cX
    cA
    wcel
    #
    wa
    #
    cB
    cA
    cR
    cX
    c-bnj14
    #
    vy
    cA
    cR
    cX
    c-bnj18
    #
    cA
    cR
    vy
    cv
    #
    c-bnj18
    #
    ciun
    #
    cun
    #
    cvv
    @2
    @3
    @7
    cA
    cR
    cX
    bnj1148
    @2
    @4
    cvv
    wcel
    @6
    cvv
    wcel
    #
    vy
    @4
    wral
    @7
    cvv
    wcel
    cA
    cR
    cX
    bnj893
    @2
    @9
    vy
    @4
    @0
    @1
    @5
    @4
    wcel
    #
    @9
    @0
    @1
    @10
    w3a
    @0
    @5
    cA
    wcel
    #
    @9
    @0
    @1
    @10
    simp1
    @10
    @0
    @11
    @1
    cA
    cR
    cX
    @5
    bnj1127
    3ad2ant3
    cA
    cR
    @5
    bnj893
    syl2anc
    3expia
    ralrimiv
    vy
    @4
    @6
    cvv
    cvv
    iunexg
    syl2anc
    bnj1149
    @2
    cB
    @3
    vy
    @3
    @6
    ciun
    #
    cun
    #
    @8
    bnj1413.1
    @2
    @3
    @4
    wss
    @12
    @7
    wss
    @13
    @8
    wss
    cA
    cR
    cX
    bnj906
    vy
    @3
    @4
    @6
    iunss1
    @12
    @7
    @3
    unss2
    3syl
    syl5eqss
    ssexd
end
