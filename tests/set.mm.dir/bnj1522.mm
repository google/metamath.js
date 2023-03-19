include "w-bnj15.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "cres.mm"
include "cop.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "wcel.mm"
include "crab.mm"
include "wbr.mm"
include "wn.mm"
include "biid.mm"
include "eqid.mm"
include "bnj1523.mm"

theorem bnj1522
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cY: class Y
  let vd: setvar d
  let vy: setvar y
  let vz: setvar z
  assume bnj1522.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1522.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1522.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1522.4: |- F = U. C

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
  disjoint H x
  disjoint R d
  disjoint R f
  disjoint R x
  disjoint Y d
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G y
  disjoint H y
  disjoint H z
  disjoint R y
  disjoint R z
  assert |- ( ( R _FrSe A /\ H Fn A /\ A. x e. A ( H ` x ) = ( G ` <. x , ( H |` _pred ( x , A , R ) ) >. ) ) -> F = H )

  proof
    cA
    cR
    w-bnj15
    cH
    cA
    wfn
    vx
    cv
    #
    cH
    cfv
    #
    @0
    cH
    cA
    cR
    @0
    c-bnj14
    cres
    cop
    cG
    cfv
    wceq
    vx
    cA
    wral
    w3a
    #
    @2
    cF
    cH
    wne
    wa
    #
    @3
    @0
    cA
    wcel
    @0
    cF
    cfv
    @1
    wne
    #
    w3a
    #
    @5
    vy
    cv
    #
    @4
    vx
    cA
    crab
    #
    wcel
    vz
    cv
    @6
    cR
    wbr
    wn
    vz
    @7
    wral
    w3a
    #
    vx
    vy
    vz
    cA
    cB
    cC
    @7
    cR
    vf
    cF
    cG
    cH
    cY
    vd
    bnj1522.1
    bnj1522.2
    bnj1522.3
    bnj1522.4
    @2
    biid
    @3
    biid
    @5
    biid
    @7
    eqid
    @8
    biid
    bnj1523
end
