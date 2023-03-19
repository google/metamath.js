include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cxp.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "opelxp.mm"
include "mpt2xopxnop0.mm"
include "sylnbir.mm"

theorem mpt2xopxprcov0
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
  disjoint V x
  disjoint W x
  disjoint F x
  disjoint K n
  disjoint F n
  disjoint V n
  disjoint W n
  disjoint X n
  disjoint Y n
  assert |- ( -. ( V e. _V /\ W e. _V ) -> ( <. V , W >. F K ) = (/) )

  proof
    cV
    cvv
    wcel
    cW
    cvv
    wcel
    wa
    cV
    cW
    cop
    #
    cvv
    cvv
    cxp
    wcel
    @0
    cK
    cF
    co
    c0
    wceq
    cV
    cW
    cvv
    cvv
    opelxp
    vx
    vy
    cC
    cF
    cK
    @0
    mpt2xopn0yelv.f
    mpt2xopxnop0
    sylnbir
end
