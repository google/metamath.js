include "wcel.mm"
include "cin.mm"
include "cdif.mm"
include "cpr.mm"
include "cv.mm"
include "wdisj.mm"
include "cvv.mm"
include "inex1g.mm"
include "elex.mm"
include "disjdifprg.mm"
include "syl2anc.mm"
include "wceq.mm"
include "difin.mm"
include "preq1i.mm"
include "a1i.mm"
include "disjeq1d.mm"
include "mpbid.mm"

theorem disjdifprg2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint A x
  disjoint B x
  assert |- ( A e. V -> Disj_ x e. { ( A \ B ) , ( A i^i B ) } x )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cA
    cB
    cin
    #
    cdif
    #
    @1
    cpr
    #
    vx
    cv
    #
    wdisj
    #
    vx
    cA
    cB
    cdif
    #
    @1
    cpr
    #
    @4
    wdisj
    @0
    @1
    cvv
    wcel
    cA
    cvv
    wcel
    @5
    cA
    cB
    cV
    inex1g
    cA
    cV
    elex
    vx
    @1
    cA
    cvv
    cvv
    disjdifprg
    syl2anc
    @0
    vx
    @3
    @7
    @4
    @3
    @7
    wceq
    @0
    @2
    @6
    @1
    cA
    cB
    difin
    preq1i
    a1i
    disjeq1d
    mpbid
end
