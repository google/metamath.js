include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "wo.mm"
include "wne.mm"
include "c0h.mm"
include "cva.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "c0v.mm"
include "chil.mm"
include "hvaddcli.mm"
include "spansnid.mm"
include "ax-mp.mm"
include "eleqtrri.mm"
include "cph.mm"
include "csh.mm"
include "spansnchi.mm"
include "chshii.mm"
include "eqeltri.mm"
include "shsleji.mm"
include "shsvai.mm"
include "mp2an.mm"
include "sselii.mm"
include "elin.mm"
include "mpbir2an.mm"
include "eleq2.mm"
include "mpbii.mm"
include "elch0.mm"
include "sylib.mm"
include "cch.mm"
include "ch0.mm"
include "syl6eqel.mm"
include "eleq2i.mm"
include "wb.mm"
include "sumspansn.mm"
include "bitr4i.mm"
include "sylibr.mm"
include "con3i.mm"
include "adantl.mm"
include "ineq12i.mm"
include "spansnm0i.mm"
include "sylnbi.mm"
include "syl5eq.mm"
include "hvcomi.mm"
include "eleq1i.mm"
include "3bitr4ri.mm"
include "oveqan12rd.mm"
include "h0elch.mm"
include "chj0i.mm"
include "syl6eq.mm"
include "eqeq2.mm"
include "notbid.mm"
include "biimparc.mm"
include "syl2anc.mm"
include "ioran.mm"
include "df-ne.mm"
include "3imtr4i.mm"

theorem nonbooli
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  assume nonbool.1: |- A e. ~H
  assume nonbool.2: |- B e. ~H
  assume nonbool.3: |- F = ( span ` { A } )
  assume nonbool.4: |- G = ( span ` { B } )
  assume nonbool.5: |- H = ( span ` { ( A +h B ) } )


  assert |- ( -. ( A e. G \/ B e. F ) -> ( H i^i ( F vH G ) ) =/= ( ( H i^i F ) vH ( H i^i G ) ) )

  proof
    cA
    cG
    wcel
    #
    wn
    #
    cB
    cF
    wcel
    #
    wn
    #
    wa
    #
    cH
    cF
    cG
    chj
    co
    #
    cin
    #
    cH
    cF
    cin
    #
    cH
    cG
    cin
    #
    chj
    co
    #
    wceq
    #
    wn
    #
    @0
    @2
    wo
    wn
    @6
    @9
    wne
    @4
    @6
    c0h
    wceq
    #
    wn
    #
    @9
    c0h
    wceq
    #
    @11
    @3
    @13
    @1
    @12
    @2
    @12
    cA
    cB
    cva
    co
    #
    cA
    csn
    cspn
    cfv
    #
    wcel
    #
    @2
    @12
    @15
    c0v
    @16
    @12
    @15
    c0h
    wcel
    #
    @15
    c0v
    wceq
    @12
    @15
    @6
    wcel
    #
    @18
    @19
    @15
    cH
    wcel
    @15
    @5
    wcel
    @15
    @15
    csn
    cspn
    cfv
    #
    cH
    @15
    chil
    wcel
    @15
    @20
    wcel
    cA
    cB
    nonbool.1
    nonbool.2
    hvaddcli
    #
    @15
    spansnid
    ax-mp
    nonbool.5
    eleqtrri
    cF
    cG
    cph
    co
    #
    @5
    @15
    cF
    cG
    cF
    @16
    csh
    nonbool.3
    @16
    cA
    nonbool.1
    spansnchi
    #
    chshii
    eqeltri
    #
    cG
    cB
    csn
    cspn
    cfv
    #
    csh
    nonbool.4
    @25
    cB
    nonbool.2
    spansnchi
    chshii
    eqeltri
    #
    shsleji
    cA
    cF
    wcel
    cB
    cG
    wcel
    @15
    @22
    wcel
    cA
    @16
    cF
    cA
    chil
    wcel
    #
    cA
    @16
    wcel
    nonbool.1
    cA
    spansnid
    ax-mp
    nonbool.3
    eleqtrri
    cB
    @25
    cG
    cB
    chil
    wcel
    #
    cB
    @25
    wcel
    nonbool.2
    cB
    spansnid
    ax-mp
    nonbool.4
    eleqtrri
    cF
    cG
    cA
    cB
    @24
    @26
    shsvai
    mp2an
    sselii
    @15
    cH
    @5
    elin
    mpbir2an
    @6
    c0h
    @15
    eleq2
    mpbii
    @15
    elch0
    sylib
    @16
    cch
    wcel
    c0v
    @16
    wcel
    @23
    @16
    ch0
    ax-mp
    syl6eqel
    @2
    cB
    @16
    wcel
    #
    @17
    cF
    @16
    cB
    nonbool.3
    eleq2i
    @27
    @28
    @17
    @29
    wb
    nonbool.1
    nonbool.2
    cA
    cB
    sumspansn
    mp2an
    bitr4i
    #
    sylibr
    con3i
    adantl
    @4
    @9
    c0h
    c0h
    chj
    co
    c0h
    @3
    @1
    @7
    c0h
    @8
    c0h
    chj
    @3
    @7
    @20
    @16
    cin
    #
    c0h
    cH
    @20
    cF
    @16
    nonbool.5
    nonbool.3
    ineq12i
    @2
    @17
    @31
    c0h
    wceq
    @30
    @15
    cA
    @21
    nonbool.1
    spansnm0i
    sylnbi
    syl5eq
    @1
    @8
    @20
    @25
    cin
    #
    c0h
    cH
    @20
    cG
    @25
    nonbool.5
    nonbool.4
    ineq12i
    @0
    @15
    @25
    wcel
    #
    @32
    c0h
    wceq
    cB
    cA
    cva
    co
    #
    @25
    wcel
    #
    cA
    @25
    wcel
    #
    @33
    @0
    @28
    @27
    @35
    @36
    wb
    nonbool.2
    nonbool.1
    cB
    cA
    sumspansn
    mp2an
    @15
    @34
    @25
    cA
    cB
    nonbool.1
    nonbool.2
    hvcomi
    eleq1i
    cG
    @25
    cA
    nonbool.4
    eleq2i
    3bitr4ri
    @15
    cB
    @21
    nonbool.2
    spansnm0i
    sylnbi
    syl5eq
    oveqan12rd
    c0h
    h0elch
    chj0i
    syl6eq
    @14
    @11
    @13
    @14
    @10
    @12
    @9
    c0h
    @6
    eqeq2
    notbid
    biimparc
    syl2anc
    @0
    @2
    ioran
    @6
    @9
    df-ne
    3imtr4i
end
