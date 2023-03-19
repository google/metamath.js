include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "csn.mm"
include "cpr.mm"
include "c1o.mm"
include "wceq.mm"
include "wn.mm"
include "dfsn2.mm"
include "id.mm"
include "syl5reqr.mm"
include "snex.mm"
include "0ex.mm"
include "preqr1.mm"
include "syl.mm"
include "snprc.mm"
include "sylibr.mm"
include "biimpi.mm"
include "preq1d.mm"
include "syl6reqr.mm"
include "impbii.mm"
include "con2bii.mm"
include "eqcom.mm"
include "bitr2i.mm"
include "sneqr.mm"
include "sneq.mm"
include "xchbinxr.mm"
include "anbi12i.mm"
include "wo.mm"
include "pm4.56.mm"
include "elpr.mm"
include "bitri.mm"
include "df1o2.mm"
include "eleq1i.mm"

theorem wopprc
  let cA: class A
  let cB: class B


  assert |- ( ( A e. _V /\ B e. _V ) <-> -. 1o e. { { { A } , (/) } , { { B } } } )

  proof
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
    c0
    csn
    #
    cA
    csn
    #
    c0
    cpr
    #
    cB
    csn
    #
    csn
    #
    cpr
    #
    wcel
    #
    c1o
    @8
    wcel
    @2
    @3
    @5
    wceq
    #
    wn
    #
    @3
    @7
    wceq
    #
    wn
    #
    wa
    #
    @9
    wn
    @0
    @11
    @1
    @13
    @10
    @0
    @10
    @0
    wn
    #
    @10
    @4
    c0
    wceq
    #
    @15
    @10
    @5
    c0
    c0
    cpr
    #
    wceq
    @16
    @10
    @17
    @3
    @5
    c0
    dfsn2
    #
    @10
    id
    syl5reqr
    @4
    c0
    c0
    cA
    snex
    0ex
    preqr1
    syl
    cA
    snprc
    #
    sylibr
    @15
    @5
    @17
    @3
    @15
    @4
    c0
    c0
    @15
    @16
    @19
    biimpi
    preq1d
    @18
    syl6reqr
    impbii
    con2bii
    @1
    c0
    @6
    wceq
    #
    @12
    @20
    @1
    @1
    wn
    @6
    c0
    wceq
    @20
    cB
    snprc
    @6
    c0
    eqcom
    bitr2i
    con2bii
    @12
    @20
    c0
    @6
    0ex
    sneqr
    c0
    @6
    sneq
    impbii
    xchbinxr
    anbi12i
    @14
    @10
    @12
    wo
    @9
    @10
    @12
    pm4.56
    @3
    @5
    @7
    c0
    snex
    elpr
    xchbinxr
    bitri
    c1o
    @3
    @8
    df1o2
    eleq1i
    xchbinxr
end
