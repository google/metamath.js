include "c1o.mm"
include "coa.mm"
include "co.mm"
include "csuc.mm"
include "c2o.mm"
include "con0.mm"
include "wcel.mm"
include "wceq.mm"
include "1on.mm"
include "oa1suc.mm"
include "ax-mp.mm"
include "df-2o.mm"
include "eqtr4i.mm"

theorem o1p1e2



  assert |- ( 1o +o 1o ) = 2o

  proof
    c1o
    c1o
    coa
    co
    #
    c1o
    csuc
    #
    c2o
    c1o
    con0
    wcel
    @0
    @1
    wceq
    1on
    c1o
    oa1suc
    ax-mp
    df-2o
    eqtr4i
end
