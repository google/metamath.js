include "cvv.mm"
include "c0.mm"
include "wne.mm"
include "cdif.mm"
include "vn0.mm"
include "wceq.mm"
include "cun.mm"
include "ssun1.mm"
include "ssv.mm"
include "eqssi.mm"
include "undif1.mm"
include "eqtr4i.mm"
include "uneq1.mm"
include "syl5eq.mm"
include "unidm.mm"
include "syl6eq.mm"
include "difabs.mm"
include "id.mm"
include "syl5req.mm"
include "difeq1.mm"
include "eqtrd.mm"
include "difid.mm"
include "necon3i.mm"
include "ax-mp.mm"

theorem compneOLD
  let cA: class A


  assert |- ( _V \ A ) =/= A

  proof
    cvv
    c0
    wne
    cvv
    cA
    cdif
    #
    cA
    wne
    vn0
    @0
    cA
    cvv
    c0
    @0
    cA
    wceq
    #
    cvv
    cA
    c0
    @1
    cvv
    cA
    cA
    cun
    #
    cA
    @1
    cvv
    @0
    cA
    cun
    #
    @2
    cvv
    cvv
    cA
    cun
    #
    @3
    cvv
    @4
    cvv
    cA
    ssun1
    @4
    ssv
    eqssi
    cvv
    cA
    undif1
    eqtr4i
    @0
    cA
    cA
    uneq1
    syl5eq
    cA
    unidm
    syl6eq
    @1
    cA
    cA
    cA
    cdif
    #
    c0
    @1
    cA
    @0
    cA
    cdif
    #
    @5
    @1
    @6
    @0
    cA
    cvv
    cA
    difabs
    @1
    id
    syl5req
    @0
    cA
    cA
    difeq1
    eqtrd
    cA
    difid
    syl6eq
    eqtrd
    necon3i
    ax-mp
end
