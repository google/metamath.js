include "cc.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "subcl.mm"
include "3adant3.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "subne0d.mm"
include "absrpcld.mm"

theorem abssubrp
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ A =/= B ) -> ( abs ` ( A - B ) ) e. RR+ )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    cA
    cB
    cmin
    co
    #
    @0
    @1
    @4
    cc
    wcel
    @2
    cA
    cB
    subcl
    3adant3
    @3
    cA
    cB
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    subne0d
    absrpcld
end
