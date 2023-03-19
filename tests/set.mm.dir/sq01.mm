include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "cmul.mm"
include "wb.mm"
include "sqval.mm"
include "mulid1.mm"
include "eqcomd.mm"
include "eqeq12d.mm"
include "adantr.mm"
include "ax-1cn.mm"
include "mulcan.mm"
include "mp3an2.mm"
include "anabss5.mm"
include "bitrd.mm"
include "biimpd.mm"
include "impancom.mm"
include "syl5bir.mm"
include "orrd.mm"
include "ex.mm"
include "sq0.mm"
include "oveq1.mm"
include "id.mm"
include "3eqtr4a.mm"
include "sq1.mm"
include "jaoi.mm"
include "impbid1.mm"

theorem sq01
  let cA: class A


  assert |- ( A e. CC -> ( ( A ^ 2 ) = A <-> ( A = 0 \/ A = 1 ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    c2
    cexp
    co
    #
    cA
    wceq
    #
    cA
    cc0
    wceq
    #
    cA
    c1
    wceq
    #
    wo
    #
    @0
    @2
    @5
    @0
    @2
    wa
    #
    @3
    @4
    @3
    wn
    cA
    cc0
    wne
    #
    @6
    @4
    cA
    cc0
    df-ne
    @0
    @7
    @2
    @4
    @0
    @7
    wa
    #
    @2
    @4
    @8
    @2
    cA
    cA
    cmul
    co
    #
    cA
    c1
    cmul
    co
    #
    wceq
    #
    @4
    @0
    @2
    @11
    wb
    @7
    @0
    @1
    @9
    cA
    @10
    cA
    sqval
    @0
    @10
    cA
    cA
    mulid1
    eqcomd
    eqeq12d
    adantr
    @0
    @7
    @11
    @4
    wb
    #
    @0
    c1
    cc
    wcel
    @8
    @12
    ax-1cn
    cA
    c1
    cA
    mulcan
    mp3an2
    anabss5
    bitrd
    biimpd
    impancom
    syl5bir
    orrd
    ex
    @3
    @2
    @4
    @3
    cc0
    c2
    cexp
    co
    cc0
    @1
    cA
    sq0
    cA
    cc0
    c2
    cexp
    oveq1
    @3
    id
    3eqtr4a
    @4
    c1
    c2
    cexp
    co
    c1
    @1
    cA
    sq1
    cA
    c1
    c2
    cexp
    oveq1
    @4
    id
    3eqtr4a
    jaoi
    impbid1
end
