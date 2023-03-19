include "wcel.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "csn.mm"
include "wceq.mm"
include "en1eqsn.mm"
include "ex.mm"
include "ensn1g.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem en1eqsnbi
  let cA: class A
  let cB: class B


  assert |- ( A e. B -> ( B ~~ 1o <-> B = { A } ) )

  proof
    cA
    cB
    wcel
    #
    cB
    c1o
    cen
    wbr
    #
    cB
    cA
    csn
    #
    wceq
    #
    @0
    @1
    @3
    cA
    cB
    en1eqsn
    ex
    @0
    @1
    @3
    @2
    c1o
    cen
    wbr
    cA
    cB
    ensn1g
    cB
    @2
    c1o
    cen
    breq1
    syl5ibrcom
    impbid
end
