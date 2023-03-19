include "com.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "con0.mm"
include "wrex.mm"
include "wlim.mm"
include "wn.mm"
include "nnlim.mm"
include "adantr.mm"
include "word.mm"
include "wi.mm"
include "nnord.mm"
include "cuni.mm"
include "wb.mm"
include "orduninsuc.mm"
include "w3a.mm"
include "df-lim.mm"
include "biimpri.mm"
include "3expia.mm"
include "sylbird.mm"
include "sylan.mm"
include "mt3d.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "peano2b.mm"
include "syl6ibr.mm"
include "ancrd.mm"
include "adantld.mm"
include "reximdv2.mm"
include "mpd.mm"

theorem nnsuc
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( ( A e. _om /\ A =/= (/) ) -> E. x e. _om A = suc x )

  proof
    cA
    com
    wcel
    #
    cA
    c0
    wne
    #
    wa
    #
    cA
    vx
    cv
    #
    csuc
    #
    wceq
    #
    vx
    con0
    wrex
    #
    @5
    vx
    com
    wrex
    #
    @2
    @6
    cA
    wlim
    #
    @0
    @8
    wn
    @1
    cA
    nnlim
    adantr
    @0
    cA
    word
    #
    @1
    @6
    wn
    #
    @8
    wi
    cA
    nnord
    @9
    @1
    wa
    @10
    cA
    cA
    cuni
    wceq
    #
    @8
    @9
    @11
    @10
    wb
    @1
    vx
    cA
    orduninsuc
    adantr
    @9
    @1
    @11
    @8
    @8
    @9
    @1
    @11
    w3a
    cA
    df-lim
    biimpri
    3expia
    sylbird
    sylan
    mt3d
    @0
    @6
    @7
    wi
    @1
    @0
    @5
    @5
    vx
    con0
    com
    @0
    @5
    @3
    com
    wcel
    #
    @5
    wa
    @3
    con0
    wcel
    @0
    @5
    @12
    @0
    @5
    @4
    com
    wcel
    #
    @12
    @5
    @0
    @13
    cA
    @4
    com
    eleq1
    biimpcd
    @3
    peano2b
    syl6ibr
    ancrd
    adantld
    reximdv2
    adantr
    mpd
end
