include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "cmoore.mm"
include "snex.mm"
include "a1i.mm"
include "cuni.mm"
include "unisng.mm"
include "snidg.mm"
include "eqeltrd.mm"
include "cv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cint.mm"
include "wi.mm"
include "wceq.mm"
include "wn.mm"
include "wo.mm"
include "df-ne.mm"
include "sssn.mm"
include "biorf.mm"
include "biimpar.mm"
include "syl2anb.mm"
include "inteq.mm"
include "intsng.mm"
include "eqtr.mm"
include "ex.mm"
include "syl2im.mm"
include "wb.mm"
include "intex.mm"
include "elsng.mm"
include "sylbi.mm"
include "biimprd.mm"
include "sylan9r.mm"
include "syldan.mm"
include "com13.mm"
include "imp31.mm"
include "bj-ismooredr2.mm"
include "snprc.mm"
include "biimpi.mm"
include "bj-0nmoore.mm"
include "eqneltrd.mm"
include "con4i.mm"
include "impbii.mm"

theorem bj-snmoore
  let cA: class A
  let vx: setvar x


  assert |- ( A e. _V <-> { A } e. Moore_ )

  proof
    cA
    cvv
    wcel
    #
    cA
    csn
    #
    cmoore
    wcel
    #
    @0
    vx
    @1
    cvv
    @1
    cvv
    wcel
    @0
    cA
    snex
    a1i
    @0
    @1
    cuni
    cA
    @1
    cA
    cvv
    unisng
    cA
    cvv
    snidg
    eqeltrd
    @0
    vx
    cv
    #
    @1
    wss
    #
    @3
    c0
    wne
    #
    @3
    cint
    #
    @1
    wcel
    #
    @5
    @4
    @0
    @7
    @5
    @4
    @0
    @7
    wi
    #
    @5
    @4
    @3
    @1
    wceq
    #
    @8
    @5
    @3
    c0
    wceq
    #
    wn
    #
    @10
    @9
    wo
    #
    @9
    @4
    @3
    c0
    df-ne
    @3
    cA
    sssn
    @11
    @9
    @12
    @10
    @9
    biorf
    biimpar
    syl2anb
    @9
    @0
    @6
    cA
    wceq
    #
    @5
    @7
    @9
    @6
    @1
    cint
    #
    wceq
    #
    @0
    @14
    cA
    wceq
    #
    @13
    @3
    @1
    inteq
    cA
    cvv
    intsng
    @15
    @16
    @13
    @6
    @14
    cA
    eqtr
    ex
    syl2im
    @5
    @7
    @13
    @5
    @6
    cvv
    wcel
    @7
    @13
    wb
    @3
    intex
    @6
    cA
    cvv
    elsng
    sylbi
    biimprd
    sylan9r
    syldan
    ex
    com13
    imp31
    bj-ismooredr2
    @0
    @2
    @0
    wn
    #
    @1
    c0
    cmoore
    @17
    @1
    c0
    wceq
    cA
    snprc
    biimpi
    c0
    cmoore
    wcel
    wn
    @17
    bj-0nmoore
    a1i
    eqneltrd
    con4i
    impbii
end
