include "cline2.mm"
include "co.mm"
include "cop.mm"
include "cfv.mm"
include "c0.mm"
include "df-ov.mm"
include "cdm.mm"
include "wcel.mm"
include "wn.mm"
include "wceq.mm"
include "cv.mm"
include "cee.mm"
include "wne.mm"
include "w3a.mm"
include "ccolin.mm"
include "ccnv.mm"
include "cec.mm"
include "wa.mm"
include "cn.mm"
include "wrex.mm"
include "wex.mm"
include "copab.mm"
include "cvv.mm"
include "neirr.mm"
include "simp3.mm"
include "mto.mm"
include "intnanr.mm"
include "a1i.mm"
include "nrex.mm"
include "nex.mm"
include "wb.mm"
include "eleq1.mm"
include "neeq1.mm"
include "3anbi13d.mm"
include "opeq1.mm"
include "eceq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "exbidv.mm"
include "neeq2.mm"
include "3anbi23d.mm"
include "opeq2.mm"
include "opelopabg.mm"
include "anidms.mm"
include "mtbiri.mm"
include "cxp.mm"
include "elopaelxp.mm"
include "opelxp1.mm"
include "syl.mm"
include "con3i.mm"
include "pm2.61i.mm"
include "coprab.mm"
include "df-line2.mm"
include "dmeqi.mm"
include "dmoprab.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "mtbir.mm"
include "ndmfv.mm"
include "ax-mp.mm"

theorem linedegen
  let cA: class A
  let vl: setvar l
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


  assert |- ( A Line A ) = (/)

  proof
    cA
    cA
    cline2
    co
    cA
    cA
    cop
    #
    cline2
    cfv
    #
    c0
    cA
    cA
    cline2
    df-ov
    @0
    cline2
    cdm
    #
    wcel
    #
    wn
    @1
    c0
    wceq
    @3
    @0
    vx
    cv
    #
    vn
    cv
    #
    cee
    cfv
    #
    wcel
    #
    vy
    cv
    #
    @6
    wcel
    #
    @4
    @8
    wne
    #
    w3a
    #
    vl
    cv
    #
    @4
    @8
    cop
    #
    ccolin
    ccnv
    #
    cec
    #
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    #
    vl
    wex
    #
    vx
    vy
    copab
    #
    wcel
    #
    cA
    cvv
    wcel
    #
    @21
    wn
    @22
    @21
    cA
    @6
    wcel
    #
    @23
    cA
    cA
    wne
    #
    w3a
    #
    @12
    @0
    @14
    cec
    #
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    #
    vl
    wex
    #
    @29
    vl
    @28
    vn
    cn
    @28
    wn
    @5
    cn
    wcel
    @25
    @27
    @25
    @24
    cA
    neirr
    @23
    @23
    @24
    simp3
    mto
    intnanr
    a1i
    nrex
    nex
    @22
    @21
    @30
    wb
    @19
    @23
    @9
    cA
    @8
    wne
    #
    w3a
    #
    @12
    cA
    @8
    cop
    #
    @14
    cec
    #
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    #
    vl
    wex
    @30
    vx
    vy
    cA
    cA
    cvv
    cvv
    @4
    cA
    wceq
    #
    @18
    @37
    vl
    @38
    @17
    @36
    vn
    cn
    @38
    @11
    @32
    @16
    @35
    @38
    @7
    @23
    @10
    @31
    @9
    @4
    cA
    @6
    eleq1
    @4
    cA
    @8
    neeq1
    3anbi13d
    @38
    @15
    @34
    @12
    @38
    @13
    @33
    @14
    @4
    cA
    @8
    opeq1
    eceq1d
    eqeq2d
    anbi12d
    rexbidv
    exbidv
    @8
    cA
    wceq
    #
    @37
    @29
    vl
    @39
    @36
    @28
    vn
    cn
    @39
    @32
    @25
    @35
    @27
    @39
    @9
    @23
    @31
    @24
    @23
    @8
    cA
    @6
    eleq1
    @8
    cA
    cA
    neeq2
    3anbi23d
    @39
    @34
    @26
    @12
    @39
    @33
    @0
    @14
    @8
    cA
    cA
    opeq2
    eceq1d
    eqeq2d
    anbi12d
    rexbidv
    exbidv
    opelopabg
    anidms
    mtbiri
    @21
    @22
    @21
    @0
    cvv
    cvv
    cxp
    wcel
    @22
    @19
    vx
    vy
    @0
    elopaelxp
    cA
    cA
    cvv
    cvv
    opelxp1
    syl
    con3i
    pm2.61i
    @2
    @20
    @0
    @2
    @18
    vx
    vy
    vl
    coprab
    #
    cdm
    @20
    cline2
    @40
    vn
    vx
    vy
    vl
    df-line2
    dmeqi
    @18
    vx
    vy
    vl
    dmoprab
    eqtri
    eleq2i
    mtbir
    @0
    cline2
    ndmfv
    ax-mp
    eqtri
end
