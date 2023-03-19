include "cima.mm"
include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wss.mm"
include "c0v.mm"
include "wa.mm"
include "cv.mm"
include "cva.mm"
include "co.mm"
include "wral.mm"
include "csm.mm"
include "cc.mm"
include "crn.mm"
include "imassrn.mm"
include "wf.mm"
include "lnopfi.mm"
include "frn.mm"
include "ax-mp.mm"
include "sstri.mm"
include "cfv.mm"
include "lnop0i.mm"
include "sh0.mm"
include "wfun.mm"
include "cdm.mm"
include "wi.mm"
include "ffun.mm"
include "shssii.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "funfvima2.mm"
include "mp2an.mm"
include "eqeltrri.mm"
include "pm3.2i.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "ralima.mm"
include "sheli.mm"
include "lnopaddi.mm"
include "syl2an.mm"
include "shaddcl.mm"
include "mp3an1.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "ralrimiva.mm"
include "oveq2.mm"
include "sylibr.mm"
include "mprgbir.mm"
include "lnopmuli.mm"
include "sylan2.mm"
include "shmulcl.mm"
include "rgen.mm"
include "issh2.mm"
include "mpbir2an.mm"

theorem imaelshi
  let cA: class A
  let cT: class T
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  assume rnelsh.1: |- T e. LinOp
  assume imaelsh.2: |- A e. SH


  assert |- ( T " A ) e. SH

  proof
    cT
    cA
    cima
    #
    csh
    wcel
    @0
    chil
    wss
    #
    c0v
    @0
    wcel
    #
    wa
    vu
    cv
    #
    vv
    cv
    #
    cva
    co
    #
    @0
    wcel
    #
    vv
    @0
    wral
    #
    vu
    @0
    wral
    #
    @3
    @4
    csm
    co
    #
    @0
    wcel
    #
    vv
    @0
    wral
    #
    vu
    cc
    wral
    #
    wa
    @1
    @2
    @0
    cT
    crn
    #
    chil
    cT
    cA
    imassrn
    chil
    chil
    cT
    wf
    #
    @13
    chil
    wss
    cT
    rnelsh.1
    lnopfi
    #
    chil
    chil
    cT
    frn
    ax-mp
    sstri
    c0v
    cT
    cfv
    #
    c0v
    @0
    cT
    rnelsh.1
    lnop0i
    c0v
    cA
    wcel
    #
    @16
    @0
    wcel
    #
    cA
    csh
    wcel
    #
    @17
    imaelsh.2
    cA
    sh0
    ax-mp
    cT
    wfun
    #
    cA
    cT
    cdm
    #
    wss
    #
    @17
    @18
    wi
    @14
    @20
    @15
    chil
    chil
    cT
    ffun
    ax-mp
    #
    cA
    chil
    @21
    cA
    imaelsh.2
    shssii
    #
    chil
    chil
    cT
    @15
    fdmi
    sseqtr4i
    #
    cA
    c0v
    cT
    funfvima2
    mp2an
    ax-mp
    eqeltrri
    pm3.2i
    @8
    @12
    @8
    vx
    cv
    #
    cT
    cfv
    #
    @4
    cva
    co
    #
    @0
    wcel
    #
    vv
    @0
    wral
    #
    vx
    cA
    cT
    chil
    wfn
    #
    cA
    chil
    wss
    #
    @8
    @30
    vx
    cA
    wral
    wb
    @14
    @31
    @15
    chil
    chil
    cT
    ffn
    ax-mp
    #
    @24
    @7
    @30
    vu
    vx
    chil
    cA
    cT
    @3
    @27
    wceq
    #
    @6
    @29
    vv
    @0
    @34
    @5
    @28
    @0
    @3
    @27
    @4
    cva
    oveq1
    eleq1d
    ralbidv
    ralima
    mp2an
    @26
    cA
    wcel
    #
    @27
    vy
    cv
    #
    cT
    cfv
    #
    cva
    co
    #
    @0
    wcel
    #
    vy
    cA
    wral
    #
    @30
    @35
    @39
    vy
    cA
    @35
    @36
    cA
    wcel
    #
    wa
    #
    @26
    @36
    cva
    co
    #
    cT
    cfv
    #
    @38
    @0
    @35
    @26
    chil
    wcel
    @36
    chil
    wcel
    #
    @44
    @38
    wceq
    @41
    @26
    cA
    imaelsh.2
    sheli
    @36
    cA
    imaelsh.2
    sheli
    #
    @26
    @36
    cT
    rnelsh.1
    lnopaddi
    syl2an
    @42
    @43
    cA
    wcel
    #
    @44
    @0
    wcel
    #
    @19
    @35
    @41
    @47
    imaelsh.2
    @26
    @36
    cA
    shaddcl
    mp3an1
    @20
    @22
    @47
    @48
    wi
    @23
    @25
    cA
    @43
    cT
    funfvima2
    mp2an
    syl
    eqeltrrd
    ralrimiva
    @31
    @32
    @30
    @40
    wb
    @33
    @24
    @29
    @39
    vv
    vy
    chil
    cA
    cT
    @4
    @37
    wceq
    #
    @28
    @38
    @0
    @4
    @37
    @27
    cva
    oveq2
    eleq1d
    ralima
    mp2an
    sylibr
    mprgbir
    @11
    vu
    cc
    @3
    cc
    wcel
    #
    @3
    @37
    csm
    co
    #
    @0
    wcel
    #
    vy
    cA
    wral
    #
    @11
    @50
    @52
    vy
    cA
    @50
    @41
    wa
    #
    @3
    @36
    csm
    co
    #
    cT
    cfv
    #
    @51
    @0
    @41
    @50
    @45
    @56
    @51
    wceq
    @46
    @3
    @36
    cT
    rnelsh.1
    lnopmuli
    sylan2
    @54
    @55
    cA
    wcel
    #
    @56
    @0
    wcel
    #
    @19
    @50
    @41
    @57
    imaelsh.2
    @3
    @36
    cA
    shmulcl
    mp3an1
    @20
    @22
    @57
    @58
    wi
    @23
    @25
    cA
    @55
    cT
    funfvima2
    mp2an
    syl
    eqeltrrd
    ralrimiva
    @31
    @32
    @11
    @53
    wb
    @33
    @24
    @10
    @52
    vv
    vy
    chil
    cA
    cT
    @49
    @9
    @51
    @0
    @4
    @37
    @3
    csm
    oveq2
    eleq1d
    ralima
    mp2an
    sylibr
    rgen
    pm3.2i
    vu
    vv
    @0
    issh2
    mpbir2an
end
