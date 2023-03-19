include "cv.mm"
include "c1.mm"
include "wceq.mm"
include "cmin.mm"
include "co.mm"
include "cn.mm"
include "wcel.mm"
include "wo.mm"
include "cc.mm"
include "caddc.mm"
include "orc.mm"
include "1cnd.mm"
include "2thd.mm"
include "eqeq1.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "orbi12d.mm"
include "ax-1cn.mm"
include "nncn.mm"
include "pncan.mm"
include "sylancl.mm"
include "id.mm"
include "eqeltrd.mm"
include "olcd.mm"
include "a1d.mm"
include "nnind.mm"

theorem nn1m1nn
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. NN -> ( A = 1 \/ ( A - 1 ) e. NN ) )

  proof
    vx
    cv
    #
    c1
    wceq
    #
    @0
    c1
    cmin
    co
    #
    cn
    wcel
    #
    wo
    #
    c1
    cc
    wcel
    #
    vy
    cv
    #
    c1
    wceq
    #
    @6
    c1
    cmin
    co
    #
    cn
    wcel
    #
    wo
    #
    @6
    c1
    caddc
    co
    #
    c1
    wceq
    #
    @11
    c1
    cmin
    co
    #
    cn
    wcel
    #
    wo
    #
    cA
    c1
    wceq
    #
    cA
    c1
    cmin
    co
    #
    cn
    wcel
    #
    wo
    vx
    vy
    cA
    @1
    @4
    @5
    @1
    @3
    orc
    @1
    1cnd
    2thd
    @0
    @6
    wceq
    #
    @1
    @7
    @3
    @9
    @0
    @6
    c1
    eqeq1
    @19
    @2
    @8
    cn
    @0
    @6
    c1
    cmin
    oveq1
    eleq1d
    orbi12d
    @0
    @11
    wceq
    #
    @1
    @12
    @3
    @14
    @0
    @11
    c1
    eqeq1
    @20
    @2
    @13
    cn
    @0
    @11
    c1
    cmin
    oveq1
    eleq1d
    orbi12d
    @0
    cA
    wceq
    #
    @1
    @16
    @3
    @18
    @0
    cA
    c1
    eqeq1
    @21
    @2
    @17
    cn
    @0
    cA
    c1
    cmin
    oveq1
    eleq1d
    orbi12d
    ax-1cn
    @6
    cn
    wcel
    #
    @15
    @10
    @22
    @14
    @12
    @22
    @13
    @6
    cn
    @22
    @6
    cc
    wcel
    @5
    @13
    @6
    wceq
    @6
    nncn
    ax-1cn
    @6
    c1
    pncan
    sylancl
    @22
    id
    eqeltrd
    olcd
    a1d
    nnind
end
