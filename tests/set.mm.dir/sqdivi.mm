include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "c2.mm"
include "cexp.mm"
include "divmuldivi.mm"
include "divcli.mm"
include "sqvali.mm"
include "oveq12i.mm"
include "3eqtr4i.mm"

theorem sqdivi
  let cA: class A
  let cB: class B
  assume sqval.1: |- A e. CC
  assume sqmul.2: |- B e. CC
  assume sqdiv.3: |- B =/= 0


  assert |- ( ( A / B ) ^ 2 ) = ( ( A ^ 2 ) / ( B ^ 2 ) )

  proof
    cA
    cB
    cdiv
    co
    #
    @0
    cmul
    co
    cA
    cA
    cmul
    co
    #
    cB
    cB
    cmul
    co
    #
    cdiv
    co
    @0
    c2
    cexp
    co
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    cdiv
    co
    cA
    cB
    cA
    cB
    sqval.1
    sqmul.2
    sqval.1
    sqmul.2
    sqdiv.3
    sqdiv.3
    divmuldivi
    @0
    cA
    cB
    sqval.1
    sqmul.2
    sqdiv.3
    divcli
    sqvali
    @3
    @1
    @4
    @2
    cdiv
    cA
    sqval.1
    sqvali
    cB
    sqmul.2
    sqvali
    oveq12i
    3eqtr4i
end
