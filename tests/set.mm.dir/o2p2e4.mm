include "c2o.mm"
include "coa.mm"
include "co.mm"
include "c3o.mm"
include "csuc.mm"
include "c4o.mm"
include "c1o.mm"
include "con0.mm"
include "wcel.mm"
include "wceq.mm"
include "2on.mm"
include "1on.mm"
include "oasuc.mm"
include "mp2an.mm"
include "df-2o.mm"
include "oveq2i.mm"
include "df-3o.mm"
include "oa1suc.mm"
include "ax-mp.mm"
include "eqtr4i.mm"
include "suceq.mm"
include "3eqtr4i.mm"
include "df-4o.mm"

theorem o2p2e4



  assert |- ( 2o +o 2o ) = 4o

  proof
    c2o
    c2o
    coa
    co
    #
    c3o
    csuc
    #
    c4o
    c2o
    c1o
    csuc
    #
    coa
    co
    #
    c2o
    c1o
    coa
    co
    #
    csuc
    #
    @0
    @1
    c2o
    con0
    wcel
    #
    c1o
    con0
    wcel
    @3
    @5
    wceq
    2on
    1on
    c2o
    c1o
    oasuc
    mp2an
    c2o
    @2
    c2o
    coa
    df-2o
    oveq2i
    c3o
    @4
    wceq
    @1
    @5
    wceq
    c3o
    c2o
    csuc
    #
    @4
    df-3o
    @6
    @4
    @7
    wceq
    2on
    c2o
    oa1suc
    ax-mp
    eqtr4i
    c3o
    @4
    suceq
    ax-mp
    3eqtr4i
    df-4o
    eqtr4i
end
