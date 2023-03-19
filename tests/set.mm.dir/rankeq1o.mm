include "crnk.mm"
include "cfv.mm"
include "c1o.mm"
include "wceq.mm"
include "c0.mm"
include "csn.mm"
include "cvv.mm"
include "wcel.mm"
include "wne.mm"
include "1n0.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "neneqd.mm"
include "fvprc.mm"
include "nsyl2.mm"
include "cv.mm"
include "wi.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "vex.mm"
include "rankeq0.mm"
include "necon3bii.mm"
include "sylibr.mm"
include "csuc.mm"
include "cr1.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "rankval.mm"
include "eqeq1i.mm"
include "cpr.mm"
include "wa.mm"
include "wss.mm"
include "ssrab2.mm"
include "elirr.mm"
include "df1o2.mm"
include "p0ex.mm"
include "eqeltri.mm"
include "id.mm"
include "syl5eleq.mm"
include "mto.mm"
include "inteq.mm"
include "int0.mm"
include "syl6eq.mm"
include "mtbiri.mm"
include "necon2ai.mm"
include "onint.mm"
include "sylancr.mm"
include "eleq1.mm"
include "mpbid.mm"
include "suceq.mm"
include "fveq2d.mm"
include "cpw.mm"
include "df-1o.mm"
include "fveq2i.mm"
include "0elon.mm"
include "r1suc.mm"
include "ax-mp.mm"
include "r10.mm"
include "pweqi.mm"
include "3eqtri.mm"
include "pw0.mm"
include "pwpw0.mm"
include "3eqtrri.mm"
include "1on.mm"
include "eqtr4i.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "elrab.mm"
include "sylib.mm"
include "wo.mm"
include "elpr.mm"
include "wn.mm"
include "df-ne.mm"
include "orel1.mm"
include "sylbi.mm"
include "eqeq2.mm"
include "eqcomd.mm"
include "syl6com.mm"
include "adantl.mm"
include "syl.mm"
include "mpd.mm"
include "vtoclg.mm"
include "mpcom.mm"
include "cdm.mm"
include "wf1.mm"
include "r111.mm"
include "f1dm.mm"
include "eleqtrri.mm"
include "rankonid.mm"
include "mpbi.mm"
include "impbii.mm"
include "eqeq2i.mm"
include "bitri.mm"

theorem rankeq1o
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( rank ` A ) = 1o <-> A = { (/) } )

  proof
    cA
    crnk
    cfv
    #
    c1o
    wceq
    #
    cA
    c1o
    wceq
    #
    cA
    c0
    csn
    #
    wceq
    @1
    @2
    cA
    cvv
    wcel
    #
    @1
    @2
    @1
    @0
    c0
    wceq
    @4
    @1
    @0
    c0
    @1
    @0
    c0
    wne
    c1o
    c0
    wne
    #
    1n0
    @0
    c1o
    c0
    neeq1
    mpbiri
    neneqd
    cA
    crnk
    fvprc
    nsyl2
    vx
    cv
    #
    crnk
    cfv
    #
    c1o
    wceq
    #
    @6
    c1o
    wceq
    #
    wi
    @1
    @2
    wi
    vx
    cA
    cvv
    @6
    cA
    wceq
    #
    @8
    @1
    @9
    @2
    @10
    @7
    @0
    c1o
    @6
    cA
    crnk
    fveq2
    eqeq1d
    @6
    cA
    c1o
    eqeq1
    imbi12d
    @8
    @6
    c0
    wne
    #
    @9
    @8
    @7
    c0
    wne
    #
    @11
    @8
    @12
    @5
    1n0
    @7
    c1o
    c0
    neeq1
    mpbiri
    @6
    c0
    @7
    c0
    @6
    vx
    vex
    #
    rankeq0
    necon3bii
    sylibr
    @8
    @6
    vy
    cv
    #
    csuc
    #
    cr1
    cfv
    #
    wcel
    #
    vy
    con0
    crab
    #
    cint
    #
    c1o
    wceq
    #
    @11
    @9
    wi
    #
    @7
    @19
    c1o
    vy
    @6
    @13
    rankval
    eqeq1i
    @20
    c1o
    con0
    wcel
    #
    @6
    c0
    @3
    cpr
    #
    wcel
    #
    wa
    #
    @21
    @20
    c1o
    @18
    wcel
    #
    @25
    @20
    @19
    @18
    wcel
    #
    @26
    @20
    @18
    con0
    wss
    @18
    c0
    wne
    @27
    @17
    vy
    con0
    ssrab2
    @20
    @18
    c0
    @18
    c0
    wceq
    #
    @20
    cvv
    c1o
    wceq
    #
    @29
    c1o
    c1o
    wcel
    c1o
    elirr
    @29
    c1o
    cvv
    c1o
    c1o
    @3
    cvv
    df1o2
    p0ex
    eqeltri
    @29
    id
    syl5eleq
    mto
    @28
    @19
    cvv
    c1o
    @28
    @19
    c0
    cint
    cvv
    @18
    c0
    inteq
    int0
    syl6eq
    eqeq1d
    mtbiri
    necon2ai
    @18
    onint
    sylancr
    @19
    c1o
    @18
    eleq1
    mpbid
    @17
    @24
    vy
    c1o
    con0
    @14
    c1o
    wceq
    #
    @16
    @23
    @6
    @30
    @16
    c1o
    csuc
    #
    cr1
    cfv
    #
    @23
    @30
    @15
    @31
    cr1
    @14
    c1o
    suceq
    fveq2d
    @23
    c1o
    cr1
    cfv
    #
    cpw
    #
    @32
    @34
    c0
    cpw
    #
    cpw
    @3
    cpw
    @23
    @33
    @35
    @33
    c0
    csuc
    #
    cr1
    cfv
    #
    c0
    cr1
    cfv
    #
    cpw
    #
    @35
    c1o
    @36
    cr1
    df-1o
    fveq2i
    c0
    con0
    wcel
    @37
    @39
    wceq
    0elon
    c0
    r1suc
    ax-mp
    @38
    c0
    r10
    pweqi
    3eqtri
    pweqi
    @35
    @3
    pw0
    pweqi
    pwpw0
    3eqtrri
    @22
    @32
    @34
    wceq
    1on
    c1o
    r1suc
    ax-mp
    eqtr4i
    syl6eqr
    eleq2d
    elrab
    sylib
    @24
    @21
    @22
    @24
    @6
    c0
    wceq
    #
    @6
    @3
    wceq
    #
    wo
    #
    @21
    @6
    c0
    @3
    @13
    elpr
    @11
    @42
    @41
    @9
    @11
    @40
    wn
    @42
    @41
    wi
    @6
    c0
    df-ne
    @40
    @41
    orel1
    sylbi
    @41
    c1o
    @6
    @41
    c1o
    @6
    wceq
    c1o
    @3
    wceq
    df1o2
    @6
    @3
    c1o
    eqeq2
    mpbiri
    eqcomd
    syl6com
    sylbi
    adantl
    syl
    sylbi
    mpd
    vtoclg
    mpcom
    @2
    @0
    c1o
    crnk
    cfv
    #
    c1o
    cA
    c1o
    crnk
    fveq2
    c1o
    cr1
    cdm
    #
    wcel
    @43
    c1o
    wceq
    c1o
    con0
    @44
    1on
    con0
    cvv
    cr1
    wf1
    @44
    con0
    wceq
    r111
    con0
    cvv
    cr1
    f1dm
    ax-mp
    eleqtrri
    c1o
    rankonid
    mpbi
    syl6eq
    impbii
    c1o
    @3
    cA
    df1o2
    eqeq2i
    bitri
end
