include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "w-bnj19.mm"
include "c-bnj14.mm"
include "wss.mm"
include "w3a.mm"
include "c-bnj18.mm"
include "cv.mm"
include "ciun.mm"
include "cun.mm"
include "eqid.mm"
include "biid.mm"
include "bnj1408.mm"

theorem bnj1414
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  assume bnj1414.1: |- B = ( _pred ( X , A , R ) u. U_ y e. _pred ( X , A , R ) _trCl ( y , A , R ) )

  disjoint A y
  disjoint R y
  disjoint X y
  assert |- ( ( R _FrSe A /\ X e. A ) -> _trCl ( X , A , R ) = B )

  proof
    cA
    cR
    w-bnj15
    cX
    cA
    wcel
    wa
    #
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
    w3a
    #
    vy
    cA
    cB
    @1
    vy
    cA
    cR
    cX
    c-bnj18
    cA
    cR
    vy
    cv
    c-bnj18
    ciun
    cun
    #
    cR
    cX
    bnj1414.1
    @3
    eqid
    @0
    biid
    @2
    biid
    bnj1408
end
