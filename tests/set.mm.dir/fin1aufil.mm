include "cfin1a.mm"
include "cfn.mm"
include "cdif.mm"
include "wcel.mm"
include "cufil.mm"
include "cfv.mm"
include "cint.mm"
include "c0.mm"
include "wceq.mm"
include "cfil.mm"
include "cv.mm"
include "wo.mm"
include "cpw.mm"
include "wral.mm"
include "wn.mm"
include "wss.mm"
include "wa.mm"
include "wb.mm"
include "eleq2i.mm"
include "eldif.mm"
include "selpw.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "a1i.mm"
include "elex.mm"
include "wsbc.mm"
include "eldifn.mm"
include "eleq1.mm"
include "notbid.mm"
include "sbcieg.mm"
include "mpbird.mm"
include "0fin.mm"
include "0ex.mm"
include "sbcie.mm"
include "con2bii.mm"
include "mpbi.mm"
include "w3a.mm"
include "wi.mm"
include "ssfi.mm"
include "expcom.mm"
include "3ad2ant3.mm"
include "con3d.mm"
include "vex.mm"
include "3imtr4g.mm"
include "cin.mm"
include "eldifi.mm"
include "fin1ai.mm"
include "sylan.mm"
include "3adant3.mm"
include "cun.mm"
include "inundif.mm"
include "incom.mm"
include "simprl.mm"
include "syl5eqel.mm"
include "simprr.mm"
include "simpl3.mm"
include "ssdifd.mm"
include "syl2anc.mm"
include "unfi.mm"
include "syl5eqelr.mm"
include "expr.mm"
include "orim2d.mm"
include "ex.mm"
include "mpid.mm"
include "anbi12i.mm"
include "ioran.mm"
include "bitr4i.mm"
include "inex1.mm"
include "isfild.mm"
include "adantr.mm"
include "ssun2.mm"
include "undif2.mm"
include "sseqtr4i.mm"
include "sylancl.mm"
include "nsyl.mm"
include "ianor.mm"
include "sylib.mm"
include "elpwi.mm"
include "adantl.mm"
include "baib.mm"
include "syl.mm"
include "difss.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "syl5bb.mm"
include "orbi12d.mm"
include "ralrimiva.mm"
include "isufil.mm"
include "sylanbrc.mm"
include "csn.mm"
include "snfi.mm"
include "eleq2s.mm"
include "mt2.mm"
include "uffixsn.mm"
include "mtoi.mm"
include "eq0rdv.mm"
include "jca.mm"

theorem fin1aufil
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume fin1aufil.1: |- F = ( ~P X \ Fin )


  assert |- ( X e. ( Fin1a \ Fin ) -> ( F e. ( UFil ` X ) /\ |^| F = (/) ) )

  proof
    cX
    cfin1a
    cfn
    cdif
    #
    wcel
    #
    cF
    cX
    cufil
    cfv
    wcel
    #
    cF
    cint
    #
    c0
    wceq
    @1
    cF
    cX
    cfil
    cfv
    wcel
    vx
    cv
    #
    cF
    wcel
    #
    cX
    @4
    cdif
    #
    cF
    wcel
    #
    wo
    #
    vx
    cX
    cpw
    #
    wral
    @2
    @1
    @4
    cfn
    wcel
    #
    wn
    #
    vx
    vy
    vz
    cX
    cF
    @5
    @4
    cX
    wss
    #
    @11
    wa
    #
    wb
    @1
    @5
    @4
    @9
    cfn
    cdif
    #
    wcel
    @4
    @9
    wcel
    #
    @11
    wa
    @13
    cF
    @14
    @4
    fin1aufil.1
    eleq2i
    @4
    @9
    cfn
    eldif
    @15
    @12
    @11
    vx
    cX
    selpw
    anbi1i
    3bitri
    #
    a1i
    cX
    @0
    elex
    @1
    @11
    vx
    cX
    wsbc
    cX
    cfn
    wcel
    #
    wn
    #
    cX
    cfin1a
    cfn
    eldifn
    #
    @11
    @18
    vx
    cX
    @0
    @4
    cX
    wceq
    @10
    @17
    @4
    cX
    cfn
    eleq1
    notbid
    sbcieg
    mpbird
    @11
    vx
    c0
    wsbc
    #
    wn
    #
    @1
    c0
    cfn
    wcel
    #
    @21
    0fin
    @20
    @22
    @11
    @22
    wn
    vx
    c0
    0ex
    @4
    c0
    wceq
    @10
    @22
    @4
    c0
    cfn
    eleq1
    notbid
    sbcie
    con2bii
    mpbi
    a1i
    @1
    vy
    cv
    #
    cX
    wss
    #
    vz
    cv
    #
    @23
    wss
    #
    w3a
    #
    @25
    cfn
    wcel
    #
    wn
    #
    @23
    cfn
    wcel
    #
    wn
    #
    @11
    vx
    @25
    wsbc
    #
    @11
    vx
    @23
    wsbc
    #
    @27
    @30
    @28
    @26
    @1
    @30
    @28
    wi
    @24
    @30
    @26
    @28
    @23
    @25
    ssfi
    expcom
    3ad2ant3
    con3d
    @11
    @29
    vx
    @25
    vz
    vex
    @4
    @25
    wceq
    @10
    @28
    @4
    @25
    cfn
    eleq1
    notbid
    sbcie
    #
    @11
    @31
    vx
    @23
    vy
    vex
    #
    @4
    @23
    wceq
    @10
    @30
    @4
    @23
    cfn
    eleq1
    notbid
    sbcie
    #
    3imtr4g
    @1
    @24
    @25
    cX
    wss
    #
    w3a
    #
    @30
    @28
    wo
    #
    wn
    #
    @23
    @25
    cin
    #
    cfn
    wcel
    #
    wn
    #
    @33
    @32
    wa
    #
    @11
    vx
    @41
    wsbc
    @38
    @42
    @39
    @38
    @42
    @30
    cX
    @23
    cdif
    #
    cfn
    wcel
    #
    wo
    #
    @39
    @1
    @24
    @47
    @37
    @1
    cX
    cfin1a
    wcel
    @24
    @47
    cX
    cfin1a
    cfn
    eldifi
    cX
    @23
    fin1ai
    sylan
    3adant3
    @38
    @42
    @47
    @39
    wi
    @38
    @42
    wa
    @46
    @28
    @30
    @38
    @42
    @46
    @28
    @38
    @42
    @46
    wa
    #
    wa
    #
    @25
    @25
    @23
    cin
    #
    @25
    @23
    cdif
    #
    cun
    #
    cfn
    @25
    @23
    inundif
    @49
    @50
    cfn
    wcel
    @51
    cfn
    wcel
    #
    @52
    cfn
    wcel
    @49
    @50
    @41
    cfn
    @25
    @23
    incom
    @38
    @42
    @46
    simprl
    syl5eqel
    @49
    @46
    @51
    @45
    wss
    @53
    @38
    @42
    @46
    simprr
    @49
    @25
    cX
    @23
    @1
    @24
    @37
    @48
    simpl3
    ssdifd
    @45
    @51
    ssfi
    syl2anc
    @50
    @51
    unfi
    syl2anc
    syl5eqelr
    expr
    orim2d
    ex
    mpid
    con3d
    @44
    @31
    @29
    wa
    @40
    @33
    @31
    @32
    @29
    @36
    @34
    anbi12i
    @30
    @28
    ioran
    bitr4i
    @11
    @43
    vx
    @41
    @23
    @25
    @35
    inex1
    @4
    @41
    wceq
    @10
    @42
    @4
    @41
    cfn
    eleq1
    notbid
    sbcie
    3imtr4g
    isfild
    @1
    @8
    vx
    @9
    @1
    @15
    wa
    #
    @8
    @11
    @6
    cfn
    wcel
    #
    wn
    #
    wo
    #
    @54
    @10
    @55
    wa
    #
    wn
    @57
    @54
    @17
    @58
    @1
    @18
    @15
    @19
    adantr
    @58
    @4
    @6
    cun
    #
    cfn
    wcel
    cX
    @59
    wss
    @17
    @4
    @6
    unfi
    cX
    @4
    cX
    cun
    @59
    cX
    @4
    ssun2
    @4
    cX
    undif2
    sseqtr4i
    @59
    cX
    ssfi
    sylancl
    nsyl
    @10
    @55
    ianor
    sylib
    @54
    @5
    @11
    @7
    @56
    @54
    @12
    @5
    @11
    wb
    @15
    @12
    @1
    @4
    cX
    elpwi
    adantl
    @5
    @12
    @11
    @16
    baib
    syl
    @7
    @6
    @14
    wcel
    #
    @54
    @56
    cF
    @14
    @6
    fin1aufil.1
    eleq2i
    @54
    @6
    @9
    wcel
    #
    @60
    @56
    wb
    @54
    @61
    @6
    cX
    wss
    #
    cX
    @4
    difss
    @1
    @61
    @62
    wb
    @15
    @6
    cX
    @0
    elpw2g
    adantr
    mpbiri
    @60
    @61
    @56
    @6
    @9
    cfn
    eldif
    baib
    syl
    syl5bb
    orbi12d
    mpbird
    ralrimiva
    vx
    cF
    cX
    isufil
    sylanbrc
    #
    @1
    vx
    @3
    @1
    @4
    @3
    wcel
    #
    @4
    csn
    #
    cF
    wcel
    #
    @66
    @65
    cfn
    wcel
    #
    @4
    snfi
    @67
    wn
    @65
    @14
    cF
    @65
    @9
    cfn
    eldifn
    fin1aufil.1
    eleq2s
    mt2
    @1
    @64
    @66
    @1
    @2
    @64
    @66
    @63
    @4
    cF
    cX
    uffixsn
    sylan
    ex
    mtoi
    eq0rdv
    jca
end
