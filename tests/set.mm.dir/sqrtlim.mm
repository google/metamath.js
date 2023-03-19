include "crp.mm"
include "c1.mm"
include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "ccxp.mm"
include "cmpt.mm"
include "csqrt.mm"
include "cfv.mm"
include "cc0.mm"
include "crli.mm"
include "wcel.mm"
include "cc.mm"
include "wceq.mm"
include "rpcn.mm"
include "cxpsqrt.mm"
include "syl.mm"
include "oveq2d.mm"
include "mpteq2ia.mm"
include "wbr.mm"
include "1rp.mm"
include "rphalfcl.mm"
include "cxplim.mm"
include "mp2b.mm"
include "eqbrtrri.mm"

theorem sqrtlim
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( n e. RR+ |-> ( 1 / ( sqrt ` n ) ) ) ~~>r 0

  proof
    vn
    crp
    c1
    vn
    cv
    #
    c1
    c2
    cdiv
    co
    #
    ccxp
    co
    #
    cdiv
    co
    #
    cmpt
    #
    vn
    crp
    c1
    @0
    csqrt
    cfv
    #
    cdiv
    co
    #
    cmpt
    cc0
    crli
    vn
    crp
    @3
    @6
    @0
    crp
    wcel
    #
    @2
    @5
    c1
    cdiv
    @7
    @0
    cc
    wcel
    @2
    @5
    wceq
    @0
    rpcn
    @0
    cxpsqrt
    syl
    oveq2d
    mpteq2ia
    c1
    crp
    wcel
    @1
    crp
    wcel
    @4
    cc0
    crli
    wbr
    1rp
    c1
    rphalfcl
    @1
    vn
    cxplim
    mp2b
    eqbrtrri
end
