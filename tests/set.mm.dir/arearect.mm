include "carea.mm"
include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cvol.mm"
include "citg.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "cdm.mm"
include "wcel.mm"
include "wceq.mm"
include "cxp.mm"
include "wss.mm"
include "ccnv.mm"
include "wral.mm"
include "cmpt.mm"
include "cibl.mm"
include "cicc.mm"
include "iccssre.mm"
include "mp2an.mm"
include "xpss12.mm"
include "eqsstri.mm"
include "cc0.mm"
include "cif.mm"
include "iftrue.mm"
include "c0.mm"
include "imaeq1i.mm"
include "xpimasn.mm"
include "eqtr4d.mm"
include "wn.mm"
include "iffalse.mm"
include "cin.mm"
include "disjsn.mm"
include "xpima1.mm"
include "sylbir.mm"
include "pm2.61i.mm"
include "eqtr4i.mm"
include "fveq2i.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "covol.mm"
include "iccmbl.mm"
include "mblvol.mm"
include "ax-mp.mm"
include "cle.mm"
include "wbr.mm"
include "ovolicc.mm"
include "mp3an.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "0mbl.mm"
include "ovol0.mm"
include "eqcomi.mm"
include "a1i.mm"
include "resubcli.mm"
include "0re.mm"
include "keepel.mm"
include "syl6eqel.mm"
include "wfun.mm"
include "wb.mm"
include "cpnf.mm"
include "wf.mm"
include "volf.mm"
include "ffun.mm"
include "eqeltri.mm"
include "fvimacnv.mm"
include "sylib.mm"
include "rgen.mm"
include "rembl.mm"
include "adantl.mm"
include "cdif.mm"
include "eldifn.mm"
include "syl.mm"
include "mpteq2ia.mm"
include "cc.mm"
include "ccncf.mm"
include "recni.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "ssid.mm"
include "cncfmptc.mm"
include "cniccibl.mm"
include "iblss2.mm"
include "dmarea.mm"
include "mpbir3an.mm"
include "areaval.mm"
include "itgeq2.mm"
include "mprg.mm"
include "itgconst.mm"
include "itgss2.mm"
include "oveq2i.mm"
include "3eqtr3i.mm"
include "mulcomi.mm"
include "3eqtri.mm"

theorem arearect
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vx: setvar x
  assume arearect.1: |- A e. RR
  assume arearect.2: |- B e. RR
  assume arearect.3: |- C e. RR
  assume arearect.4: |- D e. RR
  assume arearect.5: |- A <_ B
  assume arearect.6: |- C <_ D
  assume arearect.7: |- S = ( ( A [,] B ) X. ( C [,] D ) )


  assert |- ( area ` S ) = ( ( B - A ) x. ( D - C ) )

  proof
    cS
    carea
    cfv
    #
    vx
    cr
    cS
    vx
    cv
    #
    csn
    #
    cima
    #
    cvol
    cfv
    #
    citg
    #
    cD
    cC
    cmin
    co
    #
    cB
    cA
    cmin
    co
    #
    cmul
    co
    #
    @7
    @6
    cmul
    co
    cS
    carea
    cdm
    wcel
    #
    @0
    @5
    wceq
    @9
    cS
    cr
    cr
    cxp
    #
    wss
    @3
    cvol
    ccnv
    cr
    cima
    wcel
    #
    vx
    cr
    wral
    vx
    cr
    @4
    cmpt
    cibl
    wcel
    #
    cS
    cA
    cB
    cicc
    co
    #
    cC
    cD
    cicc
    co
    #
    cxp
    #
    @10
    arearect.7
    @13
    cr
    wss
    #
    @14
    cr
    wss
    #
    @15
    @10
    wss
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @16
    arearect.1
    arearect.2
    cA
    cB
    iccssre
    mp2an
    #
    cC
    cr
    wcel
    #
    cD
    cr
    wcel
    #
    @17
    arearect.3
    arearect.4
    cC
    cD
    iccssre
    mp2an
    @13
    cr
    @14
    cr
    xpss12
    mp2an
    eqsstri
    @11
    vx
    cr
    @1
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    @11
    @23
    @4
    @1
    @13
    wcel
    #
    @6
    cc0
    cif
    #
    cr
    @4
    @26
    wceq
    #
    @23
    @26
    @4
    @25
    @26
    @4
    wceq
    @25
    @26
    @6
    @4
    @25
    @6
    cc0
    iftrue
    @25
    @4
    @14
    cvol
    cfv
    #
    @6
    @25
    @4
    @25
    @14
    c0
    cif
    #
    cvol
    cfv
    #
    @28
    @3
    @29
    cvol
    @3
    @15
    @2
    cima
    #
    @29
    cS
    @15
    @2
    arearect.7
    imaeq1i
    @25
    @29
    @31
    wceq
    @25
    @29
    @14
    @31
    @25
    @14
    c0
    iftrue
    #
    @13
    @14
    @1
    xpimasn
    eqtr4d
    @25
    wn
    #
    @29
    c0
    @31
    @25
    @14
    c0
    iffalse
    #
    @33
    @13
    @2
    cin
    c0
    wceq
    @31
    c0
    wceq
    @13
    @1
    disjsn
    @13
    @14
    @2
    xpima1
    sylbir
    eqtr4d
    pm2.61i
    eqtr4i
    #
    fveq2i
    #
    @25
    @29
    @14
    cvol
    @32
    fveq2d
    syl5eq
    @28
    @14
    covol
    cfv
    #
    @6
    @14
    cvol
    cdm
    #
    wcel
    #
    @28
    @37
    wceq
    @21
    @22
    @39
    arearect.3
    arearect.4
    cC
    cD
    iccmbl
    mp2an
    #
    @14
    mblvol
    ax-mp
    @21
    @22
    cC
    cD
    cle
    wbr
    @37
    @6
    wceq
    arearect.3
    arearect.4
    arearect.6
    cC
    cD
    ovolicc
    mp3an
    eqtri
    syl6eq
    #
    eqtr4d
    @33
    @26
    cc0
    @4
    @25
    @6
    cc0
    iffalse
    @33
    @4
    c0
    cvol
    cfv
    #
    cc0
    @33
    @4
    @30
    @42
    @36
    @33
    @29
    c0
    cvol
    @34
    fveq2d
    syl5eq
    @42
    c0
    covol
    cfv
    #
    cc0
    c0
    @38
    wcel
    @42
    @43
    wceq
    0mbl
    c0
    mblvol
    ax-mp
    ovol0
    eqtri
    syl6eq
    #
    eqtr4d
    pm2.61i
    eqcomi
    a1i
    #
    @25
    @6
    cc0
    cr
    cD
    cC
    arearect.4
    arearect.3
    resubcli
    #
    0re
    keepel
    syl6eqel
    cvol
    wfun
    #
    @3
    @38
    wcel
    @24
    @11
    wb
    @38
    cc0
    cpnf
    cicc
    co
    #
    cvol
    wf
    @47
    volf
    @38
    @48
    cvol
    ffun
    ax-mp
    @3
    @29
    @38
    @35
    @25
    @14
    c0
    @38
    @40
    0mbl
    keepel
    eqeltri
    @3
    cr
    cvol
    fvimacnv
    mp2an
    sylib
    rgen
    cc0
    cr
    wcel
    #
    @12
    0re
    @49
    vx
    @13
    cr
    @4
    cr
    @16
    @49
    @20
    a1i
    cr
    @38
    wcel
    @49
    rembl
    a1i
    @25
    @24
    @49
    @25
    @4
    @6
    cr
    @41
    @46
    syl6eqel
    adantl
    @1
    cr
    @13
    cdif
    wcel
    #
    @4
    cc0
    wceq
    #
    @49
    @50
    @33
    @51
    @1
    cr
    @13
    eldifn
    @44
    syl
    adantl
    vx
    @13
    @4
    cmpt
    #
    cibl
    wcel
    @49
    @52
    vx
    @13
    @6
    cmpt
    #
    cibl
    vx
    @13
    @4
    @6
    @41
    mpteq2ia
    @18
    @19
    @53
    @13
    cc
    ccncf
    co
    wcel
    #
    @53
    cibl
    wcel
    arearect.1
    arearect.2
    @6
    cc
    wcel
    #
    @13
    cc
    wss
    cc
    cc
    wss
    @54
    @6
    @46
    recni
    #
    @13
    cr
    cc
    @20
    ax-resscn
    sstri
    cc
    ssid
    vx
    @6
    @13
    cc
    cncfmptc
    mp3an
    cA
    cB
    @53
    cniccibl
    mp3an
    eqeltri
    a1i
    iblss2
    ax-mp
    vx
    cS
    dmarea
    mpbir3an
    vx
    cS
    areaval
    ax-mp
    @5
    vx
    cr
    @26
    citg
    #
    @8
    @27
    @5
    @57
    wceq
    vx
    cr
    vx
    cr
    @4
    @26
    itgeq2
    @45
    mprg
    vx
    @13
    @6
    citg
    #
    @6
    @13
    cvol
    cfv
    #
    cmul
    co
    #
    @57
    @8
    @13
    @38
    wcel
    #
    @59
    cr
    wcel
    @55
    @58
    @60
    wceq
    @18
    @19
    @61
    arearect.1
    arearect.2
    cA
    cB
    iccmbl
    mp2an
    #
    @59
    @7
    cr
    @59
    @13
    covol
    cfv
    #
    @7
    @61
    @59
    @63
    wceq
    @62
    @13
    mblvol
    ax-mp
    @18
    @19
    cA
    cB
    cle
    wbr
    @63
    @7
    wceq
    arearect.1
    arearect.2
    arearect.5
    cA
    cB
    ovolicc
    mp3an
    eqtri
    #
    cB
    cA
    arearect.2
    arearect.1
    resubcli
    #
    eqeltri
    @56
    vx
    @13
    @6
    itgconst
    mp3an
    @16
    @58
    @57
    wceq
    @20
    vx
    @13
    cr
    @6
    itgss2
    ax-mp
    @59
    @7
    @6
    cmul
    @64
    oveq2i
    3eqtr3i
    eqtri
    @6
    @7
    @56
    @7
    @65
    recni
    mulcomi
    3eqtri
end
