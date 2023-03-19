include "wcel.mm"
include "wne.mm"
include "cpr.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "csn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "disjsn2.mm"
include "wi.mm"
include "c1o.mm"
include "ensn1g.mm"
include "wa.mm"
include "cun.mm"
include "pm54.43.mm"
include "df-pr.mm"
include "breq1i.mm"
include "syl6bbr.mm"
include "biimpd.mm"
include "syl2an.mm"
include "ex.mm"
include "syl7.mm"
include "3imp.mm"

theorem pr2nelem
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A e. C /\ B e. D /\ A =/= B ) -> { A , B } ~~ 2o )

  proof
    cA
    cC
    wcel
    #
    cB
    cD
    wcel
    #
    cA
    cB
    wne
    #
    cA
    cB
    cpr
    #
    c2o
    cen
    wbr
    #
    @2
    cA
    csn
    #
    cB
    csn
    #
    cin
    c0
    wceq
    #
    @0
    @1
    @4
    cA
    cB
    disjsn2
    @0
    @1
    @7
    @4
    wi
    #
    @0
    @5
    c1o
    cen
    wbr
    #
    @6
    c1o
    cen
    wbr
    #
    @8
    @1
    cA
    cC
    ensn1g
    cB
    cD
    ensn1g
    @9
    @10
    wa
    #
    @7
    @4
    @11
    @7
    @5
    @6
    cun
    #
    c2o
    cen
    wbr
    @4
    @5
    @6
    pm54.43
    @3
    @12
    c2o
    cen
    cA
    cB
    df-pr
    breq1i
    syl6bbr
    biimpd
    syl2an
    ex
    syl7
    3imp
end
