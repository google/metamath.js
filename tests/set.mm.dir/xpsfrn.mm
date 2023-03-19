include "cxp.mm"
include "c2o.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "cif.mm"
include "cixp.mm"
include "wf1o.mm"
include "wfo.mm"
include "crn.mm"
include "xpsff1o.mm"
include "f1ofo.mm"
include "forn.mm"
include "mp2b.mm"

theorem xpsfrn
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vz: setvar z
  let cV: class V
  let cX: class X
  let cY: class Y
  let cW: class W
  assume xpsff1o.f: |- F = ( x e. A , y e. B |-> `' ( { x } +c { y } ) )

  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint a b
  disjoint a k
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b k
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint k w
  disjoint k z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint F a
  disjoint F b
  disjoint F w
  disjoint F z
  disjoint V k
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint B a
  disjoint B b
  disjoint B w
  disjoint B z
  disjoint W k
  assert |- ran F = X_ k e. 2o if ( k = (/) , A , B )

  proof
    cA
    cB
    cxp
    #
    vk
    c2o
    vk
    cv
    c0
    wceq
    cA
    cB
    cif
    cixp
    #
    cF
    wf1o
    @0
    @1
    cF
    wfo
    cF
    crn
    @1
    wceq
    vx
    vy
    cA
    cB
    vk
    cF
    xpsff1o.f
    xpsff1o
    @0
    @1
    cF
    f1ofo
    @0
    @1
    cF
    forn
    mp2b
end
