include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "c2o.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "wceq.mm"
include "csn.mm"
include "dfsn2.mm"
include "c1o.mm"
include "cen.mm"
include "ensn1g.mm"
include "csdm.mm"
include "endom.mm"
include "1sdom2.mm"
include "domsdomtr.mm"
include "sdomdom.mm"
include "syl.mm"
include "sylancl.mm"
include "syl5eqbrr.mm"
include "preq2.mm"
include "breq1d.mm"
include "syl5ibr.mm"
include "eqcoms.mm"
include "adantrd.mm"
include "wne.mm"
include "pr2ne.mm"
include "biimprd.mm"
include "syl6com.mm"
include "pm2.61ine.mm"

theorem prdom2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A e. C /\ B e. D ) -> { A , B } ~<_ 2o )

  proof
    cA
    cC
    wcel
    #
    cB
    cD
    wcel
    #
    wa
    #
    cA
    cB
    cpr
    #
    c2o
    cdom
    wbr
    #
    wi
    cA
    cB
    cA
    cB
    wceq
    @0
    @4
    @1
    @0
    @4
    wi
    cB
    cA
    @0
    @4
    cB
    cA
    wceq
    #
    cA
    cA
    cpr
    #
    c2o
    cdom
    wbr
    @0
    @6
    cA
    csn
    #
    c2o
    cdom
    cA
    dfsn2
    @0
    @7
    c1o
    cen
    wbr
    #
    @7
    c2o
    cdom
    wbr
    #
    cA
    cC
    ensn1g
    @8
    @7
    c1o
    cdom
    wbr
    #
    c1o
    c2o
    csdm
    wbr
    #
    @9
    @7
    c1o
    endom
    1sdom2
    @10
    @11
    wa
    @7
    c2o
    csdm
    wbr
    @9
    @7
    c1o
    c2o
    domsdomtr
    @7
    c2o
    sdomdom
    syl
    sylancl
    syl
    syl5eqbrr
    @5
    @3
    @6
    c2o
    cdom
    cB
    cA
    cA
    preq2
    breq1d
    syl5ibr
    eqcoms
    adantrd
    @2
    cA
    cB
    wne
    #
    @3
    c2o
    cen
    wbr
    #
    @4
    @2
    @13
    @12
    cA
    cB
    cC
    cD
    pr2ne
    biimprd
    @3
    c2o
    endom
    syl6com
    pm2.61ine
end
