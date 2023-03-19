include "c1.mm"
include "ci.mm"
include "cfv.mm"
include "cr.mm"
include "cpw.mm"
include "wbr.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "c0.mm"
include "wa.mm"
include "wn.mm"
include "cv.mm"
include "c0r.mm"
include "c1r.mm"
include "cop.mm"
include "cio.mm"
include "cnr.mm"
include "csn.mm"
include "cxp.mm"
include "wcel.mm"
include "cvv.mm"
include "wceq.mm"
include "weq.mm"
include "equid.mm"
include "dfnul2.mm"
include "abeq2i.mm"
include "con2bii.mm"
include "mpbi.mm"
include "eleq1.mm"
include "mtbii.mm"
include "vtocleg.mm"
include "elex.mm"
include "con3i.mm"
include "pm2.61i.mm"
include "df-br.mm"
include "0cn.mm"
include "mulid1i.mm"
include "opeq2i.mm"
include "eleq1i.mm"
include "bitri.mm"
include "mtbir.mm"
include "intnan.mm"
include "df-i.mm"
include "fveq1i.mm"
include "df-fv.mm"
include "eqtri.mm"
include "breq2i.mm"
include "df-r.mm"
include "wss.mm"
include "cab.mm"
include "sseq2.mm"
include "abbidv.mm"
include "df-pw.mm"
include "3eqtr4g.mm"
include "ax-mp.mm"
include "breqi.mm"
include "anbi1i.mm"
include "notbii.mm"
include "mpbir.mm"

theorem avril1
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- -. ( A ~P RR ( _i ` 1 ) /\ F (/) ( 0 x. 1 ) )

  proof
    cA
    c1
    ci
    cfv
    #
    cr
    cpw
    #
    wbr
    #
    cF
    cc0
    c1
    cmul
    co
    #
    c0
    wbr
    #
    wa
    #
    wn
    cA
    c1
    vy
    cv
    c0r
    c1r
    cop
    #
    wbr
    vy
    cio
    #
    cnr
    c0r
    csn
    cxp
    #
    cpw
    #
    wbr
    #
    @4
    wa
    #
    wn
    @4
    @10
    @4
    cF
    cc0
    cop
    #
    c0
    wcel
    #
    @12
    cvv
    wcel
    #
    @13
    wn
    #
    @15
    vx
    @12
    cvv
    vx
    cv
    #
    @12
    wceq
    @16
    c0
    wcel
    #
    @13
    vx
    vx
    weq
    #
    @17
    wn
    vx
    equid
    @17
    @18
    @18
    wn
    vx
    c0
    vx
    dfnul2
    abeq2i
    con2bii
    mpbi
    @16
    @12
    c0
    eleq1
    mtbii
    vtocleg
    @13
    @14
    @12
    c0
    elex
    con3i
    pm2.61i
    @4
    cF
    @3
    cop
    #
    c0
    wcel
    @13
    cF
    @3
    c0
    df-br
    @19
    @12
    c0
    @3
    cc0
    cF
    cc0
    0cn
    mulid1i
    opeq2i
    eleq1i
    bitri
    mtbir
    intnan
    @5
    @11
    @2
    @10
    @4
    @2
    cA
    @7
    @1
    wbr
    @10
    @0
    @7
    cA
    @1
    @0
    c1
    @6
    cfv
    @7
    c1
    ci
    @6
    df-i
    fveq1i
    vy
    c1
    @6
    df-fv
    eqtri
    breq2i
    cA
    @7
    @1
    @9
    cr
    @8
    wceq
    #
    @1
    @9
    wceq
    df-r
    @20
    vz
    cv
    #
    cr
    wss
    #
    vz
    cab
    @21
    @8
    wss
    #
    vz
    cab
    @1
    @9
    @20
    @22
    @23
    vz
    cr
    @8
    @21
    sseq2
    abbidv
    vz
    cr
    df-pw
    vz
    @8
    df-pw
    3eqtr4g
    ax-mp
    breqi
    bitri
    anbi1i
    notbii
    mpbir
end
