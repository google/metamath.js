include "c0.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "0nelxp.mm"
include "mpt2xopxnop0.mm"
include "ax-mp.mm"

theorem mpt2xopx0ov0
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let vn: setvar n
  let cX: class X
  let cY: class Y
  assume mpt2xopn0yelv.f: |- F = ( x e. _V , y e. ( 1st ` x ) |-> C )

  disjoint x y
  disjoint K x
  disjoint F x
  disjoint V x
  disjoint W x
  disjoint K n
  disjoint F n
  disjoint V n
  disjoint W n
  disjoint X n
  disjoint Y n
  assert |- ( (/) F K ) = (/)

  proof
    c0
    cvv
    cvv
    cxp
    wcel
    wn
    c0
    cK
    cF
    co
    c0
    wceq
    cvv
    cvv
    0nelxp
    vx
    vy
    cC
    cF
    cK
    c0
    mpt2xopn0yelv.f
    mpt2xopxnop0
    ax-mp
end
