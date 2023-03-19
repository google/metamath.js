include "cxp.mm"
include "c2o.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "cif.mm"
include "cixp.mm"
include "wf1o.mm"
include "wf1.mm"
include "crn.mm"
include "xpsff1o.mm"
include "f1of1.mm"
include "f1f1orn.mm"
include "mp2b.mm"

theorem xpsff1o2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vw: setvar w
  let vz: setvar z
  let cV: class V
  let cX: class X
  let cY: class Y
  let cW: class W
  assume xpsff1o.f: |- F = ( x e. A , y e. B |-> `' ( { x } +c { y } ) )

  disjoint x y
  disjoint A x
  disjoint A y
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
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
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
  disjoint B k
  disjoint B w
  disjoint B z
  disjoint W k
  assert |- F : ( A X. B ) -1-1-onto-> ran F

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
    wf1
    @0
    cF
    crn
    cF
    wf1o
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
    f1of1
    @0
    @1
    cF
    f1f1orn
    mp2b
end
