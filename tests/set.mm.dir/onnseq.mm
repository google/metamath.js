include "c0.mm"
include "cfv.mm"
include "con0.mm"
include "wcel.mm"
include "cv.mm"
include "csuc.mm"
include "com.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "cmpt.mm"
include "crn.mm"
include "cin.mm"
include "wceq.mm"
include "wa.mm"
include "cep.mm"
include "wwe.mm"
include "wss.mm"
include "wne.mm"
include "epweon.mm"
include "a1i.mm"
include "wf.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "simpl.mm"
include "wi.mm"
include "suceq.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "rspcv.mm"
include "onelon.mm"
include "expcom.mm"
include "syl6.mm"
include "adantld.mm"
include "finds2.mm"
include "com12.mm"
include "ralrimiv.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylib.mm"
include "frn.mm"
include "syl.mm"
include "cdm.mm"
include "peano1.mm"
include "fdm.mm"
include "syl5eleqr.mm"
include "ne0i.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "wefrc.mm"
include "syl3anc.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "rgenw.mm"
include "cbvmptv.mm"
include "ineq2.mm"
include "eqeq1d.mm"
include "rexrnmpt.mm"
include "ax-mp.mm"
include "peano2.mm"
include "adantl.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "elrnmpt.mm"
include "sylibr.mm"
include "rspccva.mm"
include "adantll.mm"
include "inelcm.mm"
include "syl2anc.mm"
include "neneqd.mm"
include "nrexdv.mm"
include "pm2.65da.mm"
include "rexnal.mm"

theorem onnseq
  let vx: setvar x
  let cF: class F
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint F x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  assert |- ( ( F ` (/) ) e. On -> E. x e. _om -. ( F ` suc x ) e. ( F ` x ) )

  proof
    c0
    cF
    cfv
    #
    con0
    wcel
    #
    vx
    cv
    #
    csuc
    #
    cF
    cfv
    #
    @2
    cF
    cfv
    #
    wcel
    #
    vx
    com
    wral
    #
    wn
    @6
    wn
    vx
    com
    wrex
    @1
    @7
    vy
    com
    vy
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    crn
    #
    vw
    cv
    #
    cF
    cfv
    #
    cin
    #
    c0
    wceq
    #
    vw
    com
    wrex
    #
    @1
    @7
    wa
    #
    @11
    vz
    cv
    #
    cin
    #
    c0
    wceq
    #
    vz
    @11
    wrex
    #
    @16
    @17
    con0
    cep
    wwe
    #
    @11
    con0
    wss
    #
    @11
    c0
    wne
    #
    @21
    @22
    @17
    epweon
    a1i
    @17
    com
    con0
    @10
    wf
    #
    @23
    @17
    @9
    con0
    wcel
    #
    vy
    com
    wral
    @25
    @17
    @26
    vy
    com
    @8
    com
    wcel
    @17
    @26
    @26
    @1
    @18
    cF
    cfv
    #
    con0
    wcel
    #
    @18
    csuc
    #
    cF
    cfv
    #
    con0
    wcel
    #
    @17
    vy
    vz
    @8
    c0
    wceq
    @9
    @0
    con0
    @8
    c0
    cF
    fveq2
    eleq1d
    @8
    @18
    wceq
    @9
    @27
    con0
    @8
    @18
    cF
    fveq2
    eleq1d
    @8
    @29
    wceq
    @9
    @30
    con0
    @8
    @29
    cF
    fveq2
    eleq1d
    @1
    @7
    simpl
    @18
    com
    wcel
    #
    @7
    @28
    @31
    wi
    #
    @1
    @32
    @7
    @30
    @27
    wcel
    #
    @33
    @6
    @34
    vx
    @18
    com
    @2
    @18
    wceq
    #
    @4
    @30
    @5
    @27
    @35
    @3
    @29
    cF
    @2
    @18
    suceq
    fveq2d
    @2
    @18
    cF
    fveq2
    eleq12d
    rspcv
    @28
    @34
    @31
    @27
    @30
    onelon
    expcom
    syl6
    adantld
    finds2
    com12
    ralrimiv
    vy
    com
    con0
    @9
    @10
    @10
    eqid
    #
    fmpt
    sylib
    #
    com
    con0
    @10
    frn
    syl
    @17
    @10
    cdm
    #
    c0
    wne
    #
    @24
    @17
    c0
    @38
    wcel
    @39
    @17
    c0
    com
    @38
    peano1
    @17
    @25
    @38
    com
    wceq
    @37
    com
    con0
    @10
    fdm
    syl
    syl5eleqr
    @38
    c0
    ne0i
    syl
    @38
    c0
    @11
    c0
    @10
    dm0rn0
    necon3bii
    sylib
    vz
    con0
    @11
    wefrc
    syl3anc
    @13
    cvv
    wcel
    #
    vw
    com
    wral
    @21
    @16
    wb
    @40
    vw
    com
    @12
    cF
    fvex
    rgenw
    @20
    @15
    vw
    vz
    com
    @13
    @10
    cvv
    vy
    vw
    com
    @9
    @13
    @8
    @12
    cF
    fveq2
    cbvmptv
    @18
    @13
    wceq
    @19
    @14
    c0
    @18
    @13
    @11
    ineq2
    eqeq1d
    rexrnmpt
    ax-mp
    sylib
    @17
    @15
    vw
    com
    @17
    @12
    com
    wcel
    #
    wa
    #
    @14
    c0
    @42
    @12
    csuc
    #
    cF
    cfv
    #
    @11
    wcel
    #
    @44
    @13
    wcel
    #
    @14
    c0
    wne
    @42
    @44
    @9
    wceq
    #
    vy
    com
    wrex
    #
    @45
    @42
    @43
    com
    wcel
    #
    @44
    @44
    wceq
    #
    @48
    @41
    @49
    @17
    @12
    peano2
    adantl
    @44
    eqid
    @47
    @50
    vy
    @43
    com
    @8
    @43
    wceq
    @9
    @44
    @44
    @8
    @43
    cF
    fveq2
    eqeq2d
    rspcev
    sylancl
    @44
    cvv
    wcel
    @45
    @48
    wb
    @43
    cF
    fvex
    vy
    com
    @9
    @44
    @10
    cvv
    @36
    elrnmpt
    ax-mp
    sylibr
    @7
    @41
    @46
    @1
    @6
    @46
    vx
    @12
    com
    @2
    @12
    wceq
    #
    @4
    @44
    @5
    @13
    @51
    @3
    @43
    cF
    @2
    @12
    suceq
    fveq2d
    @2
    @12
    cF
    fveq2
    eleq12d
    rspccva
    adantll
    @44
    @11
    @13
    inelcm
    syl2anc
    neneqd
    nrexdv
    pm2.65da
    @6
    vx
    com
    rexnal
    sylibr
end
