include "word.mm"
include "con0.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "cvv.mm"
include "onprc.mm"
include "elex.mm"
include "mto.mm"
include "w3o.mm"
include "ordon.mm"
include "ordtri3or.mm"
include "mpan2.mm"
include "df-3or.mm"
include "sylib.mm"
include "ord.mm"
include "mt3i.mm"
include "eloni.mm"
include "ordeq.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "impbii.mm"

theorem ordeleqon
  let cA: class A


  assert |- ( Ord A <-> ( A e. On \/ A = On ) )

  proof
    cA
    word
    #
    cA
    con0
    wcel
    #
    cA
    con0
    wceq
    #
    wo
    #
    @0
    @3
    con0
    cA
    wcel
    #
    @4
    con0
    cvv
    wcel
    onprc
    con0
    cA
    elex
    mto
    @0
    @3
    @4
    @0
    @1
    @2
    @4
    w3o
    #
    @3
    @4
    wo
    @0
    con0
    word
    #
    @5
    ordon
    cA
    con0
    ordtri3or
    mpan2
    @1
    @2
    @4
    df-3or
    sylib
    ord
    mt3i
    @1
    @0
    @2
    cA
    eloni
    @2
    @0
    @6
    ordon
    cA
    con0
    ordeq
    mpbiri
    jaoi
    impbii
end
