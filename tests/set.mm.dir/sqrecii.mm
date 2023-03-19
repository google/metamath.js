include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "c2.mm"
include "cexp.mm"
include "ax-1cn.mm"
include "divmuldivi.mm"
include "1t1e1.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "reccli.mm"
include "sqvali.mm"
include "oveq2i.mm"
include "3eqtr4i.mm"

theorem sqrecii
  let cA: class A
  assume sqval.1: |- A e. CC
  assume sqreci.1: |- A =/= 0


  assert |- ( ( 1 / A ) ^ 2 ) = ( 1 / ( A ^ 2 ) )

  proof
    c1
    cA
    cdiv
    co
    #
    @0
    cmul
    co
    #
    c1
    cA
    cA
    cmul
    co
    #
    cdiv
    co
    #
    @0
    c2
    cexp
    co
    c1
    cA
    c2
    cexp
    co
    #
    cdiv
    co
    @1
    c1
    c1
    cmul
    co
    #
    @2
    cdiv
    co
    @3
    c1
    cA
    c1
    cA
    ax-1cn
    sqval.1
    ax-1cn
    sqval.1
    sqreci.1
    sqreci.1
    divmuldivi
    @5
    c1
    @2
    cdiv
    1t1e1
    oveq1i
    eqtri
    @0
    cA
    sqval.1
    sqreci.1
    reccli
    sqvali
    @4
    @2
    c1
    cdiv
    cA
    sqval.1
    sqvali
    oveq2i
    3eqtr4i
end
