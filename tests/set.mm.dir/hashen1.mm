include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "c0.mm"
include "csn.mm"
include "cen.mm"
include "wbr.mm"
include "c1o.mm"
include "cvv.mm"
include "0ex.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqeq2d.mm"
include "wa.mm"
include "simpr.mm"
include "cfn.mm"
include "wb.mm"
include "cn0.mm"
include "wi.mm"
include "1nn0.mm"
include "eqeltri.mm"
include "hashvnfin.mm"
include "mpan2.mm"
include "imp.mm"
include "snfi.mm"
include "hashen.mm"
include "sylancl.mm"
include "mpbid.mm"
include "ex.mm"
include "hasheni.mm"
include "impbid1.mm"
include "df1o2.mm"
include "breq2i.mm"
include "3bitrd.mm"

theorem hashen1
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( ( # ` A ) = 1 <-> A ~~ 1o ) )

  proof
    cA
    cV
    wcel
    #
    cA
    chash
    cfv
    #
    c1
    wceq
    @1
    c0
    csn
    #
    chash
    cfv
    #
    wceq
    #
    cA
    @2
    cen
    wbr
    #
    cA
    c1o
    cen
    wbr
    #
    @0
    c1
    @3
    @1
    c1
    @3
    wceq
    @0
    @3
    c1
    c0
    cvv
    wcel
    @3
    c1
    wceq
    0ex
    c0
    cvv
    hashsng
    ax-mp
    #
    eqcomi
    a1i
    eqeq2d
    @0
    @4
    @5
    @0
    @4
    @5
    @0
    @4
    wa
    #
    @4
    @5
    @0
    @4
    simpr
    @8
    cA
    cfn
    wcel
    #
    @2
    cfn
    wcel
    @4
    @5
    wb
    @0
    @4
    @9
    @0
    @3
    cn0
    wcel
    @4
    @9
    wi
    @3
    c1
    cn0
    @7
    1nn0
    eqeltri
    cA
    @3
    cV
    hashvnfin
    mpan2
    imp
    c0
    snfi
    cA
    @2
    hashen
    sylancl
    mpbid
    ex
    cA
    @2
    hasheni
    impbid1
    @5
    @6
    wb
    @0
    @2
    c1o
    cA
    cen
    c1o
    @2
    df1o2
    eqcomi
    breq2i
    a1i
    3bitrd
end
