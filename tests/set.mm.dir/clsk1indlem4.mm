include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "c3o.mm"
include "cpw.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "c1o.mm"
include "cpr.mm"
include "cif.mm"
include "c2o.mm"
include "ctp.mm"
include "wtru.mm"
include "cvv.mm"
include "tpex.mm"
include "a1i.mm"
include "wss.mm"
include "snsstp1.mm"
include "0ex.mm"
include "snss.mm"
include "sylibr.mm"
include "snsstp2.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "prssd.mm"
include "sselpwd.mm"
include "trud.mm"
include "df3o2.mm"
include "pweqi.mm"
include "eleqtrri.mm"
include "id.mm"
include "ifcld.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "eqeq1.mm"
include "eqcom.mm"
include "eqif.mm"
include "bitri.mm"
include "syl6bb.mm"
include "ifbieq2d.mm"
include "1n0.mm"
include "dfsn2.mm"
include "eqeq1i.mm"
include "wb.mm"
include "preq2b.mm"
include "3bitri.mm"
include "nemtbir.mm"
include "intnan.mm"
include "pm3.24.mm"
include "anbi2ci.mm"
include "mtbi.mm"
include "pm3.2ni.mm"
include "iffalsei.mm"
include "syl6eq.mm"
include "prex.mm"
include "vex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "syl.mm"
include "weq.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"
include "rgen.mm"

theorem clsk1indlem4
  let cK: class K
  let vs: setvar s
  let vr: setvar r
  assume clsk1indlem.k: |- K = ( r e. ~P 3o |-> if ( r = { (/) } , { (/) , 1o } , r ) )

  disjoint r s
  assert |- A. s e. ~P 3o ( K ` ( K ` s ) ) = ( K ` s )

  proof
    vs
    cv
    #
    cK
    cfv
    #
    cK
    cfv
    #
    @1
    wceq
    vs
    c3o
    cpw
    #
    @0
    @3
    wcel
    #
    @0
    c0
    csn
    #
    wceq
    #
    c0
    c1o
    cpr
    #
    @0
    cif
    #
    cK
    cfv
    #
    @8
    @2
    @1
    @4
    @8
    @3
    wcel
    @9
    @8
    wceq
    @4
    @6
    @7
    @0
    @3
    @7
    @3
    wcel
    @4
    @7
    c0
    c1o
    c2o
    ctp
    #
    cpw
    #
    @3
    @7
    @11
    wcel
    wtru
    @7
    @10
    cvv
    @10
    cvv
    wcel
    wtru
    c0
    c1o
    c2o
    tpex
    a1i
    wtru
    c0
    c1o
    @10
    wtru
    @5
    @10
    wss
    #
    c0
    @10
    wcel
    @12
    wtru
    c0
    c1o
    c2o
    snsstp1
    a1i
    c0
    @10
    0ex
    snss
    sylibr
    wtru
    c1o
    csn
    @10
    wss
    #
    c1o
    @10
    wcel
    @13
    wtru
    c0
    c1o
    c2o
    snsstp2
    a1i
    c1o
    @10
    c1o
    con0
    1on
    elexi
    snss
    sylibr
    prssd
    sselpwd
    trud
    c3o
    @10
    df3o2
    pweqi
    eleqtrri
    a1i
    @4
    id
    ifcld
    vr
    @8
    vr
    cv
    #
    @5
    wceq
    #
    @7
    @14
    cif
    #
    @8
    @3
    cK
    @14
    @8
    wceq
    #
    @16
    @6
    @5
    @7
    wceq
    #
    wa
    #
    @6
    wn
    #
    @5
    @0
    wceq
    #
    wa
    #
    wo
    #
    @7
    @8
    cif
    @8
    @17
    @15
    @23
    @14
    @8
    @7
    @17
    @15
    @8
    @5
    wceq
    #
    @23
    @14
    @8
    @5
    eqeq1
    @24
    @5
    @8
    wceq
    @23
    @8
    @5
    eqcom
    @6
    @5
    @7
    @0
    eqif
    bitri
    syl6bb
    @17
    id
    ifbieq2d
    @23
    @7
    @8
    @19
    @22
    @18
    @6
    @18
    c1o
    c0
    1n0
    @18
    c0
    c0
    cpr
    #
    @7
    wceq
    #
    c0
    c1o
    wceq
    #
    c1o
    c0
    wceq
    @5
    @25
    @7
    c0
    dfsn2
    eqeq1i
    @26
    @27
    wb
    wtru
    c0
    c1o
    c0
    cvv
    con0
    c0
    cvv
    wcel
    wtru
    0ex
    a1i
    c1o
    con0
    wcel
    wtru
    1on
    a1i
    preq2b
    trud
    c0
    c1o
    eqcom
    3bitri
    nemtbir
    intnan
    @6
    @20
    wa
    @22
    @6
    pm3.24
    @6
    @21
    @20
    @0
    @5
    eqcom
    anbi2ci
    mtbi
    pm3.2ni
    iffalsei
    syl6eq
    clsk1indlem.k
    @6
    @7
    @0
    c0
    c1o
    prex
    vs
    vex
    ifex
    #
    fvmpt
    syl
    @4
    @1
    @8
    cK
    vr
    @0
    @16
    @8
    @3
    cK
    vr
    vs
    weq
    #
    @15
    @6
    @14
    @0
    @7
    @14
    @0
    @5
    eqeq1
    @29
    id
    ifbieq2d
    clsk1indlem.k
    @28
    fvmpt
    #
    fveq2d
    @30
    3eqtr4d
    rgen
end
