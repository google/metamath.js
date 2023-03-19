include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cun.mm"
include "c2o.mm"
include "csn.mm"
include "wi.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "ensn1.mm"
include "ensymi.mm"
include "entr.mm"
include "mpan2.mm"
include "wcel.mm"
include "wn.mm"
include "onirri.mm"
include "disjsn.mm"
include "mpbir.mm"
include "unen.mm"
include "mpanr2.mm"
include "ex.mm"
include "sylan2.mm"
include "csuc.mm"
include "df-2o.mm"
include "df-suc.mm"
include "eqtri.mm"
include "breq2i.mm"
include "syl6ibr.mm"
include "cv.mm"
include "wex.mm"
include "en1.mm"
include "wne.mm"
include "csdm.mm"
include "unidm.mm"
include "sneq.mm"
include "uneq2d.mm"
include "syl5reqr.mm"
include "vex.mm"
include "1sdom2.mm"
include "ensdomtr.mm"
include "mp2an.mm"
include "syl6eqbr.mm"
include "sdomnen.mm"
include "syl.mm"
include "necon2ai.mm"
include "disjsn2.mm"
include "a1i.mm"
include "uneq12.mm"
include "breq1d.mm"
include "ineq12.mm"
include "eqeq1d.mm"
include "3imtr4d.mm"
include "exlimdv.mm"
include "exlimiv.mm"
include "imp.mm"
include "syl2anb.mm"
include "impbid.mm"

theorem pm54.43
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A ~~ 1o /\ B ~~ 1o ) -> ( ( A i^i B ) = (/) <-> ( A u. B ) ~~ 2o ) )

  proof
    cA
    c1o
    cen
    wbr
    #
    cB
    c1o
    cen
    wbr
    #
    wa
    #
    cA
    cB
    cin
    #
    c0
    wceq
    #
    cA
    cB
    cun
    #
    c2o
    cen
    wbr
    #
    @2
    @4
    @5
    c1o
    c1o
    csn
    #
    cun
    #
    cen
    wbr
    #
    @6
    @1
    @0
    cB
    @7
    cen
    wbr
    #
    @4
    @9
    wi
    @1
    c1o
    @7
    cen
    wbr
    @10
    @7
    c1o
    c1o
    c1o
    con0
    1on
    elexi
    ensn1
    ensymi
    cB
    c1o
    @7
    entr
    mpan2
    @0
    @10
    wa
    #
    @4
    @9
    @11
    @4
    c1o
    @7
    cin
    c0
    wceq
    #
    @9
    @12
    c1o
    c1o
    wcel
    wn
    c1o
    1on
    onirri
    c1o
    c1o
    disjsn
    mpbir
    cA
    c1o
    cB
    @7
    unen
    mpanr2
    ex
    sylan2
    c2o
    @8
    @5
    cen
    c2o
    c1o
    csuc
    @8
    df-2o
    c1o
    df-suc
    eqtri
    breq2i
    syl6ibr
    @0
    cA
    vx
    cv
    #
    csn
    #
    wceq
    #
    vx
    wex
    #
    cB
    vy
    cv
    #
    csn
    #
    wceq
    #
    vy
    wex
    #
    @6
    @4
    wi
    #
    @1
    vx
    cA
    en1
    vy
    cB
    en1
    @16
    @20
    @21
    @15
    @20
    @21
    wi
    vx
    @15
    @19
    @21
    vy
    @15
    @19
    @21
    @15
    @19
    wa
    #
    @14
    @18
    cun
    #
    c2o
    cen
    wbr
    #
    @14
    @18
    cin
    #
    c0
    wceq
    #
    @6
    @4
    @24
    @26
    wi
    @22
    @24
    @13
    @17
    wne
    @26
    @24
    @13
    @17
    @13
    @17
    wceq
    #
    @23
    c2o
    csdm
    wbr
    @24
    wn
    @27
    @23
    @14
    c2o
    csdm
    @27
    @14
    @14
    @14
    cun
    @23
    @14
    unidm
    @27
    @14
    @18
    @14
    @13
    @17
    sneq
    uneq2d
    syl5reqr
    @14
    c1o
    cen
    wbr
    c1o
    c2o
    csdm
    wbr
    @14
    c2o
    csdm
    wbr
    @13
    vx
    vex
    ensn1
    1sdom2
    @14
    c1o
    c2o
    ensdomtr
    mp2an
    syl6eqbr
    @23
    c2o
    sdomnen
    syl
    necon2ai
    @13
    @17
    disjsn2
    syl
    a1i
    @22
    @5
    @23
    c2o
    cen
    cA
    @14
    cB
    @18
    uneq12
    breq1d
    @22
    @3
    @25
    c0
    cA
    @14
    cB
    @18
    ineq12
    eqeq1d
    3imtr4d
    ex
    exlimdv
    exlimiv
    imp
    syl2anb
    impbid
end
