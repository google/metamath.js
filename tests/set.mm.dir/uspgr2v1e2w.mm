include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "cvv.mm"
include "cs1.mm"
include "cop.mm"
include "cuspgr.mm"
include "prex.mm"
include "a1i.mm"
include "prid1g.mm"
include "adantr.mm"
include "prid2g.mm"
include "adantl.mm"
include "uspgr1ewop.mm"
include "syl3anc.mm"

theorem uspgr2v1e2w
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y


  assert |- ( ( A e. X /\ B e. Y ) -> <. { A , B } , <" { A , B } "> >. e. USPGraph )

  proof
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    wa
    #
    cA
    cB
    cpr
    #
    cvv
    wcel
    #
    cA
    @3
    wcel
    #
    cB
    @3
    wcel
    #
    @3
    @3
    cs1
    cop
    cuspgr
    wcel
    @4
    @2
    cA
    cB
    prex
    a1i
    @0
    @5
    @1
    cA
    cB
    cX
    prid1g
    adantr
    @1
    @6
    @0
    cA
    cB
    cY
    prid2g
    adantl
    cA
    cB
    @3
    cvv
    uspgr1ewop
    syl3anc
end
