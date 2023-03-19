include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cc.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmpt.mm"
include "cdv.mm"
include "c1.mm"
include "cmin.mm"
include "cmul.mm"
include "cif.mm"
include "elnn0.mm"
include "dvexp.mm"
include "nnne0.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "mpteq2dv.mm"
include "eqtr4d.mm"
include "csn.mm"
include "cxp.mm"
include "oveq2.mm"
include "exp0.mm"
include "sylan9eq.mm"
include "mpteq2dva.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "ax-1cn.mm"
include "dvconst.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "iftrue.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem dvexp2
  let vx: setvar x
  let cN: class N

  disjoint N x
  assert |- ( N e. NN0 -> ( CC _D ( x e. CC |-> ( x ^ N ) ) ) = ( x e. CC |-> if ( N = 0 , 0 , ( N x. ( x ^ ( N - 1 ) ) ) ) ) )

  proof
    cN
    cn0
    wcel
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    cc
    vx
    cc
    vx
    cv
    #
    cN
    cexp
    co
    #
    cmpt
    #
    cdv
    co
    #
    vx
    cc
    @1
    cc0
    cN
    @2
    cN
    c1
    cmin
    co
    cexp
    co
    cmul
    co
    #
    cif
    #
    cmpt
    #
    wceq
    #
    cN
    elnn0
    @0
    @9
    @1
    @0
    @5
    vx
    cc
    @6
    cmpt
    @8
    vx
    cN
    dvexp
    @0
    vx
    cc
    @7
    @6
    @0
    @1
    cc0
    @6
    @0
    cN
    cc0
    cN
    nnne0
    neneqd
    iffalsed
    mpteq2dv
    eqtr4d
    @1
    @5
    vx
    cc
    cc0
    cmpt
    #
    @8
    @1
    @5
    cc
    cc0
    csn
    cxp
    #
    @10
    @1
    @5
    cc
    cc
    c1
    csn
    cxp
    #
    cdv
    co
    #
    @11
    @1
    @4
    @12
    cc
    cdv
    @1
    @4
    vx
    cc
    c1
    cmpt
    @12
    @1
    vx
    cc
    @3
    c1
    @1
    @2
    cc
    wcel
    @3
    @2
    cc0
    cexp
    co
    c1
    cN
    cc0
    @2
    cexp
    oveq2
    @2
    exp0
    sylan9eq
    mpteq2dva
    vx
    cc
    c1
    fconstmpt
    syl6eqr
    oveq2d
    c1
    cc
    wcel
    @13
    @11
    wceq
    ax-1cn
    c1
    dvconst
    ax-mp
    syl6eq
    vx
    cc
    cc0
    fconstmpt
    syl6eq
    @1
    vx
    cc
    @7
    cc0
    @1
    cc0
    @6
    iftrue
    mpteq2dv
    eqtr4d
    jaoi
    sylbi
end
