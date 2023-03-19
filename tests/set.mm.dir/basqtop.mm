include "ctb.mm"
include "wcel.mm"
include "wf1o.mm"
include "wa.mm"
include "cv.mm"
include "cin.mm"
include "cqtop.mm"
include "co.mm"
include "cpw.mm"
include "cuni.mm"
include "wss.mm"
include "wral.mm"
include "ccnv.mm"
include "cima.mm"
include "wfo.mm"
include "wb.mm"
include "f1ofo.mm"
include "elqtop2.mm"
include "anbi12d.mm"
include "sylan2.mm"
include "w3a.mm"
include "cfv.mm"
include "wrex.mm"
include "simpl1l.mm"
include "simpl2r.mm"
include "simpl3r.mm"
include "wfn.mm"
include "simpl1r.mm"
include "f1ocnv.mm"
include "f1ofn.mm"
include "3syl.mm"
include "simpl2l.mm"
include "inss1.mm"
include "simpr.mm"
include "sseldi.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "simpl3l.mm"
include "inss2.mm"
include "elind.mm"
include "basis2.mm"
include "syl22anc.mm"
include "wceq.mm"
include "adantr.mm"
include "simp2l.mm"
include "syl5ss.mm"
include "sselda.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "syl.mm"
include "simprrr.mm"
include "syl6ss.mm"
include "cdm.mm"
include "cnvimass.mm"
include "f1odm.mm"
include "syl5sseq.mm"
include "sstrd.mm"
include "simprrl.mm"
include "eqeltrrd.mm"
include "crn.mm"
include "imassrn.mm"
include "forn.mm"
include "wf1.mm"
include "f1of1.mm"
include "f1imacnv.mm"
include "simprl.mm"
include "eqeltrd.mm"
include "mpbir2and.mm"
include "wfun.mm"
include "fnfun.mm"
include "inpreima.mm"
include "sseqtr4d.mm"
include "funimass3.mm"
include "mpbird.mm"
include "vex.mm"
include "inex1.mm"
include "elpw2.mm"
include "sylibr.mm"
include "elunii.mm"
include "rexlimddv.mm"
include "ex.mm"
include "ssrdv.mm"
include "3expib.mm"
include "sylbid.mm"
include "ralrimivv.mm"
include "cvv.mm"
include "ovex.mm"
include "isbasisg.mm"
include "ax-mp.mm"

theorem basqtop
  let cF: class F
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume qtopcmp.1: |- X = U. J


  assert |- ( ( J e. TopBases /\ F : X -1-1-onto-> Y ) -> ( J qTop F ) e. TopBases )

  proof
    cJ
    ctb
    wcel
    #
    cX
    cY
    cF
    wf1o
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    cJ
    cF
    cqtop
    co
    #
    @5
    cpw
    #
    cin
    #
    cuni
    #
    wss
    #
    vy
    @6
    wral
    vx
    @6
    wral
    #
    @6
    ctb
    wcel
    #
    @2
    @10
    vx
    vy
    @6
    @6
    @2
    @3
    @6
    wcel
    #
    @4
    @6
    wcel
    #
    wa
    #
    @3
    cY
    wss
    #
    cF
    ccnv
    #
    @3
    cima
    #
    cJ
    wcel
    #
    wa
    #
    @4
    cY
    wss
    #
    @17
    @4
    cima
    #
    cJ
    wcel
    #
    wa
    #
    wa
    #
    @10
    @1
    @0
    cX
    cY
    cF
    wfo
    #
    @15
    @25
    wb
    cX
    cY
    cF
    f1ofo
    #
    @0
    @26
    wa
    @13
    @20
    @14
    @24
    @3
    cF
    cJ
    ctb
    cX
    cY
    qtopcmp.1
    elqtop2
    @4
    cF
    cJ
    ctb
    cX
    cY
    qtopcmp.1
    elqtop2
    anbi12d
    sylan2
    @2
    @20
    @24
    @10
    @2
    @20
    @24
    w3a
    #
    vz
    @5
    @9
    @28
    vz
    cv
    #
    @5
    wcel
    #
    @29
    @9
    wcel
    #
    @28
    @30
    wa
    #
    @29
    @17
    cfv
    #
    vw
    cv
    #
    wcel
    #
    @34
    @18
    @22
    cin
    #
    wss
    #
    wa
    #
    @31
    vw
    cJ
    @32
    @0
    @19
    @23
    @33
    @36
    wcel
    @38
    vw
    cJ
    wrex
    @0
    @1
    @20
    @24
    @30
    simpl1l
    #
    @16
    @19
    @2
    @24
    @30
    simpl2r
    @21
    @23
    @2
    @20
    @30
    simpl3r
    @32
    @18
    @22
    @33
    @32
    @17
    cY
    wfn
    #
    @16
    @29
    @3
    wcel
    @33
    @18
    wcel
    @32
    @1
    cY
    cX
    @17
    wf1o
    @40
    @0
    @1
    @20
    @24
    @30
    simpl1r
    #
    cX
    cY
    cF
    f1ocnv
    cY
    cX
    @17
    f1ofn
    3syl
    #
    @16
    @19
    @2
    @24
    @30
    simpl2l
    @32
    @5
    @3
    @29
    @3
    @4
    inss1
    #
    @28
    @30
    simpr
    #
    sseldi
    cY
    @3
    @17
    @29
    fnfvima
    syl3anc
    @32
    @40
    @21
    @29
    @4
    wcel
    @33
    @22
    wcel
    @42
    @21
    @23
    @2
    @20
    @30
    simpl3l
    @32
    @5
    @4
    @29
    @3
    @4
    inss2
    @44
    sseldi
    cY
    @4
    @17
    @29
    fnfvima
    syl3anc
    elind
    vw
    @33
    cJ
    @18
    @22
    basis2
    syl22anc
    @32
    @34
    cJ
    wcel
    #
    @38
    wa
    #
    wa
    #
    @29
    cF
    @34
    cima
    #
    wcel
    @48
    @8
    wcel
    @31
    @47
    @33
    cF
    cfv
    #
    @29
    @48
    @47
    @1
    @29
    cY
    wcel
    #
    @49
    @29
    wceq
    @32
    @1
    @46
    @41
    adantr
    #
    @32
    @50
    @46
    @28
    @5
    cY
    @29
    @28
    @5
    @3
    cY
    @43
    @2
    @16
    @19
    @24
    simp2l
    syl5ss
    sselda
    adantr
    cX
    cY
    @29
    cF
    f1ocnvfv2
    syl2anc
    @47
    cF
    cX
    wfn
    #
    @34
    cX
    wss
    #
    @35
    @49
    @48
    wcel
    @47
    @1
    @52
    @51
    cX
    cY
    cF
    f1ofn
    syl
    #
    @47
    @34
    @18
    cX
    @47
    @34
    @36
    @18
    @32
    @45
    @35
    @37
    simprrr
    #
    @18
    @22
    inss1
    syl6ss
    #
    @47
    cF
    cdm
    #
    @18
    cX
    cF
    @3
    cnvimass
    #
    @47
    @1
    @57
    cX
    wceq
    @51
    cX
    cY
    cF
    f1odm
    syl
    syl5sseq
    sstrd
    #
    @32
    @45
    @35
    @37
    simprrl
    cX
    @34
    cF
    @33
    fnfvima
    syl3anc
    eqeltrrd
    @47
    @6
    @7
    @48
    @47
    @48
    @6
    wcel
    #
    @48
    cY
    wss
    #
    @17
    @48
    cima
    #
    cJ
    wcel
    #
    @47
    cF
    crn
    #
    @48
    cY
    cF
    @34
    imassrn
    @47
    @26
    @64
    cY
    wceq
    @47
    @1
    @26
    @51
    @27
    syl
    #
    cX
    cY
    cF
    forn
    syl
    syl5sseq
    @47
    @62
    @34
    cJ
    @47
    cX
    cY
    cF
    wf1
    #
    @53
    @62
    @34
    wceq
    @47
    @1
    @66
    @51
    cX
    cY
    cF
    f1of1
    syl
    @59
    cX
    cY
    @34
    cF
    f1imacnv
    syl2anc
    @32
    @45
    @38
    simprl
    eqeltrd
    @47
    @0
    @26
    @60
    @61
    @63
    wa
    wb
    @32
    @0
    @46
    @39
    adantr
    @65
    @48
    cF
    cJ
    ctb
    cX
    cY
    qtopcmp.1
    elqtop2
    syl2anc
    mpbir2and
    @47
    @48
    @5
    wss
    #
    @48
    @7
    wcel
    @47
    @67
    @34
    @17
    @5
    cima
    #
    wss
    #
    @47
    @34
    @36
    @68
    @55
    @47
    @52
    cF
    wfun
    #
    @68
    @36
    wceq
    @54
    cX
    cF
    fnfun
    #
    @3
    @4
    cF
    inpreima
    3syl
    sseqtr4d
    @47
    @70
    @34
    @57
    wss
    @67
    @69
    wb
    @47
    @52
    @70
    @54
    @71
    syl
    @47
    @34
    @18
    @57
    @56
    @58
    syl6ss
    @34
    @5
    cF
    funimass3
    syl2anc
    mpbird
    @48
    @5
    @3
    @4
    vx
    vex
    inex1
    elpw2
    sylibr
    elind
    @29
    @48
    @8
    elunii
    syl2anc
    rexlimddv
    ex
    ssrdv
    3expib
    sylbid
    ralrimivv
    @6
    cvv
    wcel
    @12
    @11
    wb
    cJ
    cF
    cqtop
    ovex
    vx
    vy
    @6
    cvv
    isbasisg
    ax-mp
    sylibr
end
