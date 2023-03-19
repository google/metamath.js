include "w-bnj15.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "w3a.mm"
include "wceq.mm"
include "biid.mm"
include "bnj1501.mm"

theorem bnj1500
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cY: class Y
  let vd: setvar d
  assume bnj1500.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1500.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1500.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1500.4: |- F = U. C

  disjoint A d
  disjoint A f
  disjoint A x
  disjoint d f
  disjoint d x
  disjoint f x
  disjoint B f
  disjoint G d
  disjoint G f
  disjoint G x
  disjoint R d
  disjoint R f
  disjoint R x
  disjoint Y d
  assert |- ( R _FrSe A -> A. x e. A ( F ` x ) = ( G ` <. x , ( F |` _pred ( x , A , R ) ) >. ) )

  proof
    cA
    cR
    w-bnj15
    vx
    cv
    #
    cA
    wcel
    wa
    #
    @1
    vf
    cv
    #
    cC
    wcel
    @0
    @2
    cdm
    #
    wcel
    w3a
    #
    @4
    vd
    cv
    #
    cB
    wcel
    @3
    @5
    wceq
    w3a
    #
    vx
    cA
    cB
    cC
    cR
    vf
    cF
    cG
    cY
    vd
    bnj1500.1
    bnj1500.2
    bnj1500.3
    bnj1500.4
    @1
    biid
    @4
    biid
    @6
    biid
    bnj1501
end
