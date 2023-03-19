include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "cop.mm"
include "cpr.mm"
include "cuspgr.mm"
include "dfsn2.mm"
include "opeq2i.mm"
include "sneqi.mm"
include "wa.mm"
include "3simpa.mm"
include "id.mm"
include "ancri.mm"
include "3ad2ant3.mm"
include "uspgr1eop.mm"
include "syl2anc.mm"
include "syl5eqel.mm"

theorem uspgr1v1eop
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( V e. W /\ A e. X /\ B e. V ) -> <. V , { <. A , { B } >. } >. e. USPGraph )

  proof
    cV
    cW
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cV
    wcel
    #
    w3a
    #
    cV
    cA
    cB
    csn
    #
    cop
    #
    csn
    #
    cop
    cV
    cA
    cB
    cB
    cpr
    #
    cop
    #
    csn
    #
    cop
    #
    cuspgr
    @6
    @9
    cV
    @5
    @8
    @4
    @7
    cA
    cB
    dfsn2
    opeq2i
    sneqi
    opeq2i
    @3
    @0
    @1
    wa
    @2
    @2
    wa
    #
    @10
    cuspgr
    wcel
    @0
    @1
    @2
    3simpa
    @2
    @0
    @11
    @1
    @2
    @2
    @2
    id
    ancri
    3ad2ant3
    cA
    cB
    cB
    cV
    cW
    cX
    uspgr1eop
    syl2anc
    syl5eqel
end
