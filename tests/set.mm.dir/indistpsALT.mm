include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "cpr.mm"
include "ctopon.mm"
include "cfv.mm"
include "ctps.mm"
include "indistopon.mm"
include "cbs.mm"
include "wceq.mm"
include "cts.mm"
include "c9.mm"
include "df-tset.mm"
include "1lt9.mm"
include "9nn.mm"
include "2strbas.mm"
include "ax-mp.mm"
include "prex.mm"
include "2strop.mm"
include "tsettps.mm"
include "mp2b.mm"

theorem indistpsALT
  let cA: class A
  let cK: class K
  assume indistpsALT.a: |- A e. _V
  assume indistpsALT.k: |- K = { <. ( Base ` ndx ) , A >. , <. ( TopSet ` ndx ) , { (/) , A } >. }


  assert |- K e. TopSp

  proof
    cA
    cvv
    wcel
    #
    c0
    cA
    cpr
    #
    cA
    ctopon
    cfv
    wcel
    cK
    ctps
    wcel
    indistpsALT.a
    cA
    cvv
    indistopon
    cA
    @1
    cK
    @0
    cA
    cK
    cbs
    cfv
    wceq
    indistpsALT.a
    cA
    @1
    cts
    cK
    c9
    cvv
    indistpsALT.k
    df-tset
    1lt9
    9nn
    2strbas
    ax-mp
    @1
    cvv
    wcel
    @1
    cK
    cts
    cfv
    wceq
    c0
    cA
    prex
    cA
    @1
    cts
    cK
    c9
    cvv
    indistpsALT.k
    df-tset
    1lt9
    9nn
    2strop
    ax-mp
    tsettps
    mp2b
end
