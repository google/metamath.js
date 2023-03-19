include "cv.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "wceq.mm"
include "wa.mm"
include "sneq.mm"
include "oveqan12d.mm"
include "cnveqd.mm"
include "ovex.mm"
include "cnvex.mm"
include "ovmpt2a.mm"

theorem xpsfval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vw: setvar w
  let vz: setvar z
  let cV: class V
  let cW: class W
  assume xpsff1o.f: |- F = ( x e. A , y e. B |-> `' ( { x } +c { y } ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
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
  disjoint B a
  disjoint B b
  disjoint B k
  disjoint B w
  disjoint B z
  disjoint W k
  assert |- ( ( X e. A /\ Y e. B ) -> ( X F Y ) = `' ( { X } +c { Y } ) )

  proof
    vx
    vy
    cX
    cY
    cA
    cB
    vx
    cv
    #
    csn
    #
    vy
    cv
    #
    csn
    #
    ccda
    co
    #
    ccnv
    cX
    csn
    #
    cY
    csn
    #
    ccda
    co
    #
    ccnv
    cF
    @0
    cX
    wceq
    #
    @2
    cY
    wceq
    #
    wa
    @4
    @7
    @8
    @9
    @1
    @5
    @3
    @6
    ccda
    @0
    cX
    sneq
    @2
    cY
    sneq
    oveqan12d
    cnveqd
    xpsff1o.f
    @7
    @5
    @6
    ccda
    ovex
    cnvex
    ovmpt2a
end
