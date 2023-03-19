include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "c-bnj18.mm"
include "wss.mm"
include "biimpri.mm"
include "cvv.mm"
include "w-bnj19.mm"
include "c-bnj14.mm"
include "cv.mm"
include "ciun.mm"
include "cun.mm"
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
include "syl5eqel.mm"
include "bnj1137.mm"
include "bnj931.mm"
include "a1i.mm"
include "syl3anbrc.mm"
include "bnj1124.mm"
include "bnj906.mm"
include "bnj1125.mm"
include "ss2iun.mm"
include "bnj1143.mm"
include "syl6ss.mm"
include "syl.mm"
include "unssd.mm"
include "syl5eqss.mm"
include "eqssd.mm"

theorem bnj1136
  let wth: wff th
  let wta: wff ta
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  assume bnj1136.1: |- B = ( _pred ( X , A , R ) u. U_ y e. _trCl ( X , A , R ) _trCl ( y , A , R ) )
  assume bnj1136.2: |- ( th <-> ( R _FrSe A /\ X e. A ) )
  assume bnj1136.3: |- ( ta <-> ( B e. _V /\ _TrFo ( B , A , R ) /\ _pred ( X , A , R ) C_ B ) )

  disjoint A y
  disjoint R y
  disjoint X y
  assert |- ( ( R _FrSe A /\ X e. A ) -> _trCl ( X , A , R ) = B )

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
    cA
    cR
    cX
    c-bnj18
    #
    cB
    @2
    wth
    wta
    @3
    cB
    wss
    wth
    @2
    bnj1136.2
    biimpri
    @2
    cB
    cvv
    wcel
    cA
    cB
    cR
    w-bnj19
    cA
    cR
    cX
    c-bnj14
    #
    cB
    wss
    #
    wta
    @2
    cB
    @4
    vy
    @3
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
    bnj1136.1
    @2
    @4
    @8
    cA
    cR
    cX
    bnj1148
    @2
    @3
    cvv
    wcel
    @7
    cvv
    wcel
    #
    vy
    @3
    wral
    @8
    cvv
    wcel
    cA
    cR
    cX
    bnj893
    @2
    @10
    vy
    @3
    @0
    @1
    @6
    @3
    wcel
    #
    @10
    @0
    @1
    @11
    w3a
    @0
    @6
    cA
    wcel
    #
    @10
    @0
    @1
    @11
    simp1
    @11
    @0
    @12
    @1
    cA
    cR
    cX
    @6
    bnj1127
    3ad2ant3
    cA
    cR
    @6
    bnj893
    syl2anc
    3expia
    ralrimiv
    vy
    @3
    @7
    cvv
    cvv
    iunexg
    syl2anc
    bnj1149
    syl5eqel
    vy
    cA
    cB
    cR
    cX
    bnj1136.1
    bnj1137
    @5
    @2
    cB
    @4
    @8
    bnj1136.1
    bnj931
    a1i
    bnj1136.3
    syl3anbrc
    wth
    wta
    cA
    cB
    cR
    cX
    bnj1136.2
    bnj1136.3
    bnj1124
    syl2anc
    @2
    cB
    @9
    @3
    bnj1136.1
    @2
    @4
    @8
    @3
    cA
    cR
    cX
    bnj906
    @2
    @7
    @3
    wss
    #
    vy
    @3
    wral
    #
    @8
    @3
    wss
    @2
    @13
    vy
    @3
    @0
    @1
    @11
    @13
    cA
    cR
    cX
    @6
    bnj1125
    3expia
    ralrimiv
    @14
    @8
    vy
    @3
    @3
    ciun
    @3
    vy
    @3
    @7
    @3
    ss2iun
    vy
    @3
    @3
    bnj1143
    syl6ss
    syl
    unssd
    syl5eqss
    eqssd
end
