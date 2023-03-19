include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wnel.mm"
include "cop.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "mpt2xopynvov0g.mm"
include "ex.mm"
include "wn.mm"
include "mpt2xopxprcov0.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem mpt2xopynvov0
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
  assert |- ( K e/ V -> ( <. V , W >. F K ) = (/) )

  proof
    cV
    cvv
    wcel
    cW
    cvv
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
    c0
    wceq
    #
    wi
    @0
    @1
    @2
    vx
    vy
    cC
    cF
    cK
    cV
    cW
    cvv
    cvv
    mpt2xopn0yelv.f
    mpt2xopynvov0g
    ex
    @0
    wn
    @2
    @1
    vx
    vy
    cC
    cF
    cK
    cV
    cW
    mpt2xopn0yelv.f
    mpt2xopxprcov0
    a1d
    pm2.61i
end
