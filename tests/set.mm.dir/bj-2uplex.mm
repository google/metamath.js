include "bj-c2uple.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "bj-cpr1.mm"
include "bj-pr21val.mm"
include "bj-pr1ex.mm"
include "syl5eqelr.mm"
include "bj-cpr2.mm"
include "bj-pr22val.mm"
include "bj-pr2ex.mm"
include "jca.mm"
include "bj-c1upl.mm"
include "c1o.mm"
include "csn.mm"
include "bj-ctag.mm"
include "cxp.mm"
include "cun.mm"
include "df-bj-2upl.mm"
include "bj-1uplex.mm"
include "biimpri.mm"
include "wi.mm"
include "snex.mm"
include "bj-xtagex.mm"
include "ax-mp.mm"
include "unexg.mm"
include "syl2an.mm"
include "syl5eqel.mm"
include "impbii.mm"

theorem bj-2uplex
  let cA: class A
  let cB: class B


  assert |- ( (| A ,, B |) e. _V <-> ( A e. _V /\ B e. _V ) )

  proof
    cA
    cB
    bj-c2uple
    #
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    #
    @1
    @2
    @3
    @1
    cA
    @0
    bj-cpr1
    cvv
    cA
    cB
    bj-pr21val
    @0
    cvv
    bj-pr1ex
    syl5eqelr
    @1
    cB
    @0
    bj-cpr2
    cvv
    cA
    cB
    bj-pr22val
    @0
    cvv
    bj-pr2ex
    syl5eqelr
    jca
    @4
    @0
    cA
    bj-c1upl
    #
    c1o
    csn
    #
    cB
    bj-ctag
    cxp
    #
    cun
    #
    cvv
    cA
    cB
    df-bj-2upl
    @2
    @5
    cvv
    wcel
    #
    @7
    cvv
    wcel
    #
    @8
    cvv
    wcel
    @3
    @9
    @2
    cA
    bj-1uplex
    biimpri
    @6
    cvv
    wcel
    @3
    @10
    wi
    c1o
    snex
    @6
    cB
    cvv
    cvv
    bj-xtagex
    ax-mp
    @5
    @7
    cvv
    cvv
    unexg
    syl2an
    syl5eqel
    impbii
end
