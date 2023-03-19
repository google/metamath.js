include "wcel.mm"
include "wa.mm"
include "wnel.mm"
include "cop.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "cv.mm"
include "wex.mm"
include "neq0.mm"
include "mpt2xopn0yelv.mm"
include "nnel.mm"
include "syl6ibr.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "con4d.mm"
include "imp.mm"

theorem mpt2xopynvov0g
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vn: setvar n
  assume mpt2xopn0yelv.f: |- F = ( x e. _V , y e. ( 1st ` x ) |-> C )

  disjoint x y
  disjoint K x
  disjoint V x
  disjoint W x
  disjoint K n
  disjoint F n
  disjoint V n
  disjoint W n
  disjoint X n
  disjoint Y n
  assert |- ( ( ( V e. X /\ W e. Y ) /\ K e/ V ) -> ( <. V , W >. F K ) = (/) )

  proof
    cV
    cX
    wcel
    cW
    cY
    wcel
    wa
    #
    cK
    cV
    wnel
    #
    cV
    cW
    cop
    cK
    cF
    co
    #
    c0
    wceq
    #
    @0
    @3
    @1
    @3
    wn
    vn
    cv
    #
    @2
    wcel
    #
    vn
    wex
    @0
    @1
    wn
    #
    vn
    @2
    neq0
    @0
    @5
    @6
    vn
    @0
    @5
    cK
    cV
    wcel
    @6
    vx
    vy
    cC
    cF
    cK
    @4
    cV
    cW
    cX
    cY
    mpt2xopn0yelv.f
    mpt2xopn0yelv
    cK
    cV
    nnel
    syl6ibr
    exlimdv
    syl5bi
    con4d
    imp
end
