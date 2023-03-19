include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cmin.mm"
include "wlklenvp1.mm"
include "wa.mm"
include "oveq1.mm"
include "cc.mm"
include "wcel.mm"
include "wlkcl.mm"
include "nn0cnd.mm"
include "pncan1.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "eqcomd.mm"
include "mpdan.mm"

theorem wlklenvm1
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Walks ` G ) P -> ( # ` F ) = ( ( # ` P ) - 1 ) )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cP
    chash
    cfv
    #
    cF
    chash
    cfv
    #
    c1
    caddc
    co
    #
    wceq
    #
    @2
    @1
    c1
    cmin
    co
    #
    wceq
    cP
    cF
    cG
    wlklenvp1
    @0
    @4
    wa
    @5
    @2
    @4
    @0
    @5
    @3
    c1
    cmin
    co
    #
    @2
    @1
    @3
    c1
    cmin
    oveq1
    @0
    @2
    cc
    wcel
    @6
    @2
    wceq
    @0
    @2
    cP
    cF
    cG
    wlkcl
    nn0cnd
    @2
    pncan1
    syl
    sylan9eqr
    eqcomd
    mpdan
end
