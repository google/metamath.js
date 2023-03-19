include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "c-bnj14.mm"
include "wss.mm"
include "wral.mm"
include "w-bnj19.mm"
include "c-bnj18.mm"
include "ciun.mm"
include "wo.mm"
include "cun.mm"
include "eleq2i.mm"
include "elun.mm"
include "bitri.mm"
include "bnj213.mm"
include "sseli.mm"
include "bnj906.mm"
include "adantlr.mm"
include "sylan2.mm"
include "sselda.mm"
include "bnj18eq1.mm"
include "ssiun2s.mm"
include "syl.mm"
include "sstrd.mm"
include "bnj1147.mm"
include "rgenw.mm"
include "iunss.mm"
include "mpbir.mm"
include "bnj1125.mm"
include "3expia.mm"
include "ralrimiv.mm"
include "sylibr.mm"
include "jaodan.mm"
include "ssun2.mm"
include "sseqtr4i.mm"
include "syl6ss.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "df-bnj19.mm"

theorem bnj1137
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  let vv: setvar v
  assume bnj1137.1: |- B = ( _pred ( X , A , R ) u. U_ y e. _trCl ( X , A , R ) _trCl ( y , A , R ) )

  disjoint A y
  disjoint R y
  disjoint X y
  disjoint v y
  disjoint A v
  disjoint B v
  disjoint R v
  disjoint X v
  assert |- ( ( R _FrSe A /\ X e. A ) -> _TrFo ( B , A , R ) )

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
    vv
    cv
    #
    c-bnj14
    #
    cB
    wss
    #
    vv
    cB
    wral
    cA
    cB
    cR
    w-bnj19
    @2
    @5
    vv
    cB
    @3
    cB
    wcel
    #
    @2
    @3
    cA
    cR
    cX
    c-bnj14
    #
    wcel
    #
    @3
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
    wcel
    #
    wo
    #
    @5
    @6
    @3
    @7
    @12
    cun
    #
    wcel
    @14
    cB
    @15
    @3
    bnj1137.1
    eleq2i
    @3
    @7
    @12
    elun
    bitri
    @2
    @14
    wa
    @4
    @12
    cB
    @2
    @8
    @4
    @12
    wss
    @13
    @2
    @8
    wa
    #
    @4
    cA
    cR
    @3
    c-bnj18
    #
    @12
    @8
    @2
    @3
    cA
    wcel
    #
    @4
    @17
    wss
    #
    @7
    cA
    @3
    cA
    cR
    cX
    bnj213
    sseli
    @0
    @18
    @19
    @1
    cA
    cR
    @3
    bnj906
    adantlr
    #
    sylan2
    @16
    @3
    @9
    wcel
    #
    @17
    @12
    wss
    #
    @2
    @7
    @9
    @3
    cA
    cR
    cX
    bnj906
    sselda
    vy
    @9
    @11
    @3
    @17
    cA
    cR
    @10
    @3
    bnj18eq1
    ssiun2s
    #
    syl
    sstrd
    @2
    @13
    wa
    #
    @4
    @17
    @12
    @13
    @2
    @18
    @19
    @12
    cA
    @3
    @12
    cA
    wss
    @11
    cA
    wss
    #
    vy
    @9
    wral
    @25
    vy
    @9
    cA
    cR
    @10
    bnj1147
    rgenw
    vy
    @9
    @11
    cA
    iunss
    mpbir
    sseli
    @20
    sylan2
    @24
    @21
    @22
    @2
    @12
    @9
    @3
    @2
    @11
    @9
    wss
    #
    vy
    @9
    wral
    @12
    @9
    wss
    @2
    @26
    vy
    @9
    @0
    @1
    @10
    @9
    wcel
    @26
    cA
    cR
    cX
    @10
    bnj1125
    3expia
    ralrimiv
    vy
    @9
    @11
    @9
    iunss
    sylibr
    sselda
    @23
    syl
    sstrd
    jaodan
    @12
    @15
    cB
    @12
    @7
    ssun2
    bnj1137.1
    sseqtr4i
    syl6ss
    sylan2b
    ralrimiva
    vv
    cA
    cB
    cR
    df-bnj19
    sylibr
end
