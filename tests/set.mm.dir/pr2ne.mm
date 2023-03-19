include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "preq2.mm"
include "eqcoms.mm"
include "wi.mm"
include "c1o.mm"
include "enpr1g.mm"
include "entr.mm"
include "csdm.mm"
include "1sdom2.mm"
include "sdomnen.mm"
include "ax-mp.mm"
include "ensym.mm"
include "ex.mm"
include "syl.mm"
include "mtoi.mm"
include "a1d.mm"
include "cvv.mm"
include "prex.mm"
include "eqeng.mm"
include "syl11.mm"
include "a1dd.mm"
include "com23.mm"
include "imp.mm"
include "pm2.43a.mm"
include "syl5.mm"
include "necon2ad.mm"
include "pr2nelem.mm"
include "3expia.mm"
include "impbid.mm"

theorem pr2ne
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A e. C /\ B e. D ) -> ( { A , B } ~~ 2o <-> A =/= B ) )

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
    cen
    wbr
    #
    cA
    cB
    wne
    #
    @2
    @4
    cA
    cB
    cA
    cB
    wceq
    @3
    cA
    cA
    cpr
    #
    wceq
    #
    @2
    @4
    wn
    #
    @7
    cB
    cA
    cB
    cA
    cA
    preq2
    eqcoms
    @7
    @2
    @8
    @0
    @1
    @7
    @2
    @8
    wi
    #
    wi
    @0
    @7
    @1
    @9
    @0
    @6
    c1o
    cen
    wbr
    #
    @7
    @1
    @9
    wi
    wi
    cA
    cC
    enpr1g
    @10
    @7
    @9
    @1
    @3
    @6
    cen
    wbr
    #
    @10
    @9
    @7
    @11
    @10
    @9
    @11
    @10
    wa
    @3
    c1o
    cen
    wbr
    #
    @9
    @3
    @6
    c1o
    entr
    @12
    @8
    @2
    @12
    @4
    c1o
    c2o
    cen
    wbr
    #
    c1o
    c2o
    csdm
    wbr
    @13
    wn
    1sdom2
    c1o
    c2o
    sdomnen
    ax-mp
    @12
    c1o
    @3
    cen
    wbr
    #
    @4
    @13
    wi
    @3
    c1o
    ensym
    @14
    @4
    @13
    c1o
    @3
    c2o
    entr
    ex
    syl
    mtoi
    a1d
    syl
    ex
    @3
    cvv
    wcel
    @7
    @11
    wi
    cA
    cB
    prex
    @3
    @6
    cvv
    eqeng
    ax-mp
    syl11
    a1dd
    syl
    com23
    imp
    pm2.43a
    syl5
    necon2ad
    @0
    @1
    @5
    @4
    cA
    cB
    cC
    cD
    pr2nelem
    3expia
    impbid
end
