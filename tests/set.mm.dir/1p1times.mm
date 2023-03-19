include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "1cnd.mm"
include "id.mm"
include "cmul.mm"
include "mulid2.mm"
include "oveq12d.mm"
include "joinlmuladdmuld.mm"

theorem 1p1times
  let cA: class A


  assert |- ( A e. CC -> ( ( 1 + 1 ) x. A ) = ( A + A ) )

  proof
    cA
    cc
    wcel
    #
    c1
    cA
    c1
    cA
    cA
    caddc
    co
    @0
    1cnd
    #
    @0
    id
    @1
    @0
    c1
    cA
    cmul
    co
    #
    cA
    @2
    cA
    caddc
    cA
    mulid2
    #
    @3
    oveq12d
    joinlmuladdmuld
end
