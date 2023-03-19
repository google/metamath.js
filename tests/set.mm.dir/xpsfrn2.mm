include "wcel.mm"
include "wa.mm"
include "c2o.mm"
include "cv.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cfv.mm"
include "cixp.mm"
include "c0.mm"
include "wceq.mm"
include "cif.mm"
include "crn.mm"
include "xpscfv.mm"
include "3expa.mm"
include "ixpeq2dva.mm"
include "xpsfrn.mm"
include "syl6reqr.mm"

theorem xpsfrn2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vz: setvar z
  let cX: class X
  let cY: class Y
  assume xpsff1o.f: |- F = ( x e. A , y e. B |-> `' ( { x } +c { y } ) )

  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint V k
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint W k
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
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint B a
  disjoint B b
  disjoint B w
  disjoint B z
  assert |- ( ( A e. V /\ B e. W ) -> ran F = X_ k e. 2o ( `' ( { A } +c { B } ) ` k ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    vk
    c2o
    vk
    cv
    #
    cA
    csn
    cB
    csn
    ccda
    co
    ccnv
    cfv
    #
    cixp
    vk
    c2o
    @3
    c0
    wceq
    cA
    cB
    cif
    #
    cixp
    cF
    crn
    @2
    vk
    c2o
    @4
    @5
    @0
    @1
    @3
    c2o
    wcel
    @4
    @5
    wceq
    cA
    cB
    @3
    cV
    cW
    xpscfv
    3expa
    ixpeq2dva
    vx
    vy
    cA
    cB
    vk
    cF
    xpsff1o.f
    xpsfrn
    syl6reqr
end
