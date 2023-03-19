include "com.mm"
include "cr1.mm"
include "cima.mm"
include "cres.mm"
include "wf1.mm"
include "cvv.mm"
include "wcel.mm"
include "wf1o.mm"
include "con0.mm"
include "wss.mm"
include "r111.mm"
include "omsson.mm"
include "f1ores.mm"
include "mp2an.mm"
include "f1of1.mm"
include "ax-mp.mm"
include "c0.mm"
include "cv.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "wel.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "wfn.mm"
include "wb.mm"
include "r1fnon.mm"
include "fvelimab.mm"
include "csuc.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "weq.mm"
include "r10.mm"
include "eleq1i.mm"
include "biimpri.mm"
include "adantr.mm"
include "pweq.mm"
include "rspccv.mm"
include "nnon.mm"
include "r1suc.mm"
include "syl.mm"
include "biimprcd.mm"
include "syl6.mm"
include "com3r.mm"
include "adantld.mm"
include "finds2.mm"
include "eleq1.mm"
include "biimpd.mm"
include "syl9.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "com12.mm"
include "ssrdv.mm"
include "vex.mm"
include "ssex.mm"
include "wex.mm"
include "0ex.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "csdm.mm"
include "wbr.mm"
include "w3a.mm"
include "axgroth6.mm"
include "simpr.mm"
include "ralimi.mm"
include "anim2i.mm"
include "3adant3.mm"
include "eximii.mm"
include "vtocl.mm"
include "exlimiiv.mm"
include "f1dmex.mm"

theorem grothomex
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u


  assert |- _om e. _V

  proof
    com
    cr1
    com
    cima
    #
    cr1
    com
    cres
    #
    wf1
    #
    @0
    cvv
    wcel
    #
    com
    cvv
    wcel
    com
    @0
    @1
    wf1o
    #
    @2
    con0
    cvv
    cr1
    wf1
    com
    con0
    wss
    #
    @4
    r111
    omsson
    con0
    cvv
    com
    cr1
    f1ores
    mp2an
    com
    @0
    @1
    f1of1
    ax-mp
    c0
    vy
    cv
    #
    wcel
    #
    vz
    cv
    #
    cpw
    #
    @6
    wcel
    #
    vz
    @6
    wral
    #
    wa
    #
    @3
    vy
    @12
    @0
    @6
    wss
    @3
    @12
    vw
    @0
    @6
    vw
    cv
    #
    @0
    wcel
    #
    @12
    vw
    vy
    wel
    #
    @14
    vx
    cv
    #
    cr1
    cfv
    #
    @13
    wceq
    #
    vx
    com
    wrex
    #
    @12
    @15
    wi
    #
    cr1
    con0
    wfn
    @5
    @14
    @19
    wb
    r1fnon
    omsson
    vx
    con0
    com
    @13
    cr1
    fvelimab
    mp2an
    @18
    @20
    vx
    com
    @16
    com
    wcel
    @12
    @17
    @6
    wcel
    #
    @18
    @15
    @21
    c0
    cr1
    cfv
    #
    @6
    wcel
    #
    @13
    cr1
    cfv
    #
    @6
    wcel
    #
    @13
    csuc
    #
    cr1
    cfv
    #
    @6
    wcel
    #
    @12
    vx
    vw
    @16
    c0
    wceq
    #
    @17
    @22
    @6
    @16
    c0
    cr1
    fveq2
    eleq1d
    vx
    vw
    weq
    @17
    @24
    @6
    @16
    @13
    cr1
    fveq2
    eleq1d
    @16
    @26
    wceq
    @17
    @27
    @6
    @16
    @26
    cr1
    fveq2
    eleq1d
    @7
    @23
    @11
    @23
    @7
    @22
    c0
    @6
    r10
    eleq1i
    biimpri
    adantr
    @13
    com
    wcel
    #
    @11
    @25
    @28
    wi
    @7
    @11
    @25
    @30
    @28
    @11
    @25
    @24
    cpw
    #
    @6
    wcel
    #
    @30
    @28
    wi
    @10
    @32
    vz
    @24
    @6
    @8
    @24
    wceq
    @9
    @31
    @6
    @8
    @24
    pweq
    eleq1d
    rspccv
    @30
    @28
    @32
    @30
    @27
    @31
    @6
    @30
    @13
    con0
    wcel
    @27
    @31
    wceq
    @13
    nnon
    @13
    r1suc
    syl
    eleq1d
    biimprcd
    syl6
    com3r
    adantld
    finds2
    @18
    @21
    @15
    @17
    @13
    @6
    eleq1
    biimpd
    syl9
    rexlimiv
    sylbi
    com12
    ssrdv
    @0
    @6
    vy
    vex
    ssex
    syl
    vx
    vy
    wel
    #
    @11
    wa
    #
    vy
    wex
    @12
    vy
    wex
    vx
    c0
    0ex
    @29
    @34
    @12
    vy
    @29
    @33
    @7
    @11
    @16
    c0
    @6
    eleq1
    anbi1d
    exbidv
    @33
    @9
    @6
    wss
    #
    @10
    wa
    #
    vz
    @6
    wral
    #
    @8
    @6
    csdm
    wbr
    vz
    vy
    wel
    wi
    vz
    @6
    cpw
    wral
    #
    w3a
    @34
    vy
    vx
    vy
    vz
    axgroth6
    @33
    @37
    @34
    @38
    @37
    @11
    @33
    @36
    @10
    vz
    @6
    @35
    @10
    simpr
    ralimi
    anim2i
    3adant3
    eximii
    vtocl
    exlimiiv
    com
    @0
    cvv
    @1
    f1dmex
    mp2an
end
