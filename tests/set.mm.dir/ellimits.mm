include "climits.mm"
include "wcel.mm"
include "con0.mm"
include "cbigcup.mm"
include "cfix.mm"
include "cin.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "wa.mm"
include "wlim.mm"
include "df-limits.mm"
include "eleq2i.mm"
include "eldif.mm"
include "word.mm"
include "wne.mm"
include "cuni.mm"
include "wceq.mm"
include "w3a.mm"
include "3anan32.mm"
include "df-lim.mm"
include "elin.mm"
include "elon.mm"
include "wbr.mm"
include "elfix.mm"
include "brbigcup.mm"
include "eqcom.mm"
include "3bitri.mm"
include "anbi12i.mm"
include "bitri.mm"
include "elsn.mm"
include "necon3bbii.mm"
include "3bitr4ri.mm"

theorem ellimits
  let cA: class A
  assume ellimits.1: |- A e. _V


  assert |- ( A e. Limits <-> Lim A )

  proof
    cA
    climits
    wcel
    cA
    con0
    cbigcup
    cfix
    #
    cin
    #
    c0
    csn
    #
    cdif
    #
    wcel
    cA
    @1
    wcel
    #
    cA
    @2
    wcel
    #
    wn
    #
    wa
    #
    cA
    wlim
    #
    climits
    @3
    cA
    df-limits
    eleq2i
    cA
    @1
    @2
    eldif
    cA
    word
    #
    cA
    c0
    wne
    #
    cA
    cA
    cuni
    #
    wceq
    #
    w3a
    @9
    @12
    wa
    #
    @10
    wa
    @8
    @7
    @9
    @10
    @12
    3anan32
    cA
    df-lim
    @4
    @13
    @6
    @10
    @4
    cA
    con0
    wcel
    #
    cA
    @0
    wcel
    #
    wa
    @13
    cA
    con0
    @0
    elin
    @14
    @9
    @15
    @12
    cA
    ellimits.1
    elon
    @15
    cA
    cA
    cbigcup
    wbr
    @11
    cA
    wceq
    @12
    cA
    cbigcup
    ellimits.1
    elfix
    cA
    cA
    ellimits.1
    brbigcup
    @11
    cA
    eqcom
    3bitri
    anbi12i
    bitri
    @5
    cA
    c0
    cA
    c0
    ellimits.1
    elsn
    necon3bbii
    anbi12i
    3bitr4ri
    3bitri
end
