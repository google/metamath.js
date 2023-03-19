include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cpr.mm"
include "cima.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "cin.mm"
include "c0.mm"
include "cs1.mm"
include "fveq2i.mm"
include "s1len.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "fzo0.mm"
include "imaeq2i.mm"
include "ineq2i.mm"
include "ima0.mm"
include "in0.mm"

theorem 1pthdlem2
  let cP: class P
  let cF: class F
  let cJ: class J
  let cX: class X
  let cY: class Y
  assume 1wlkd.p: |- P = <" X Y ">
  assume 1wlkd.f: |- F = <" J ">


  assert |- ( ( P " { 0 , ( # ` F ) } ) i^i ( P " ( 1 ..^ ( # ` F ) ) ) ) = (/)

  proof
    cP
    cc0
    cF
    chash
    cfv
    #
    cpr
    cima
    #
    cP
    c1
    @0
    cfzo
    co
    #
    cima
    #
    cin
    @1
    cP
    c0
    cima
    #
    cin
    #
    c0
    @3
    @4
    @1
    @2
    c0
    cP
    @2
    c1
    c1
    cfzo
    co
    c0
    @0
    c1
    c1
    cfzo
    @0
    cJ
    cs1
    #
    chash
    cfv
    c1
    cF
    @6
    chash
    1wlkd.f
    fveq2i
    cJ
    s1len
    eqtri
    oveq2i
    c1
    fzo0
    eqtri
    imaeq2i
    ineq2i
    @5
    @1
    c0
    cin
    c0
    @4
    c0
    @1
    cP
    ima0
    ineq2i
    @1
    in0
    eqtri
    eqtri
end
