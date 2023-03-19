include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cfi.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cint.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "wb.mm"
include "ovex.mm"
include "elfi2.mm"
include "ax-mp.mm"
include "wf.mm"
include "wral.mm"
include "wex.mm"
include "eldifi.mm"
include "adantl.mm"
include "wss.mm"
include "elfpw.mm"
include "simprbi.mm"
include "syl.mm"
include "simplbi.mm"
include "sseld.mm"
include "elrest.mm"
include "adantr.mm"
include "sylibd.mm"
include "ralrimiv.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "ac6sfi.mm"
include "syl2anc.mm"
include "ciin.mm"
include "wne.mm"
include "eldifsni.mm"
include "ad2antlr.mm"
include "iinin1.mm"
include "fvex.mm"
include "a1i.mm"
include "simpllr.mm"
include "crn.mm"
include "wfn.mm"
include "ffn.mm"
include "fniinfv.mm"
include "simplll.mm"
include "simpr.mm"
include "intrnfi.mm"
include "syl13anc.mm"
include "eqeltrd.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "intiin.mm"
include "iineq2.mm"
include "syl5eq.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "mpd.mm"
include "eleq1.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "sylancr.mm"
include "wi.mm"
include "ineq1i.mm"
include "syl6eqr.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "ssralv.mm"
include "sylc.mm"
include "iinfi.mm"
include "eqeltrrd.mm"
include "imbi1d.mm"
include "sylbid.mm"
include "rexlimdv.mm"
include "impbid.mm"
include "eqrdv.mm"
include "wn.mm"
include "fi0.mm"
include "cdm.mm"
include "wrel.mm"
include "cxp.mm"
include "relxp.mm"
include "restfn.mm"
include "fndm.mm"
include "releqi.mm"
include "mpbir.mm"
include "ovprc.mm"
include "fveq2d.mm"
include "wo.mm"
include "ianor.mm"
include "fvprc.mm"
include "oveq1d.mm"
include "0rest.mm"
include "syl6eq.mm"
include "ovprc2.mm"
include "jaoi.mm"
include "sylbi.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem firest
  let cA: class A
  let cJ: class J
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cV: class V


  assert |- ( fi ` ( J |`t A ) ) = ( ( fi ` J ) |`t A )

  proof
    cJ
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    wa
    #
    cJ
    cA
    crest
    co
    #
    cfi
    cfv
    #
    cJ
    cfi
    cfv
    #
    cA
    crest
    co
    #
    wceq
    @2
    vx
    @4
    @6
    @2
    vx
    cv
    #
    @4
    wcel
    #
    @7
    @6
    wcel
    #
    @8
    @7
    vy
    cv
    #
    cint
    #
    wceq
    #
    vy
    @3
    cpw
    cfn
    cin
    #
    c0
    csn
    #
    cdif
    #
    wrex
    #
    @2
    @9
    @3
    cvv
    wcel
    #
    @8
    @16
    wb
    cJ
    cA
    crest
    ovex
    #
    vy
    @7
    @3
    cvv
    elfi2
    ax-mp
    @2
    @12
    @9
    vy
    @15
    @2
    @10
    @15
    wcel
    #
    wa
    #
    @9
    @12
    @11
    @6
    wcel
    #
    @20
    @10
    cJ
    vf
    cv
    #
    wf
    #
    vz
    cv
    #
    @24
    @22
    cfv
    #
    cA
    cin
    #
    wceq
    #
    vz
    @10
    wral
    #
    wa
    #
    vf
    wex
    #
    @21
    @20
    @10
    cfn
    wcel
    #
    @24
    @10
    cA
    cin
    #
    wceq
    #
    vy
    cJ
    wrex
    #
    vz
    @10
    wral
    @30
    @20
    @10
    @13
    wcel
    #
    @31
    @19
    @35
    @2
    @10
    @13
    @14
    eldifi
    adantl
    #
    @35
    @10
    @3
    wss
    #
    @31
    @10
    @3
    elfpw
    #
    simprbi
    syl
    #
    @20
    @34
    vz
    @10
    @20
    @24
    @10
    wcel
    @24
    @3
    wcel
    #
    @34
    @20
    @10
    @3
    @24
    @20
    @35
    @37
    @36
    @35
    @37
    @31
    @38
    simplbi
    syl
    sseld
    @2
    @40
    @34
    wb
    @19
    vy
    @24
    cA
    cJ
    cvv
    cvv
    elrest
    adantr
    sylibd
    ralrimiv
    @33
    @27
    vz
    vy
    @10
    cJ
    vf
    @10
    @25
    wceq
    @32
    @26
    @24
    @10
    @25
    cA
    ineq1
    eqeq2d
    ac6sfi
    syl2anc
    @20
    @29
    @21
    vf
    @20
    @23
    @28
    @21
    @20
    @23
    wa
    #
    @21
    @28
    vz
    @10
    @26
    ciin
    #
    @6
    wcel
    @41
    @42
    vz
    @10
    @25
    ciin
    #
    cA
    cin
    #
    @6
    @41
    @10
    c0
    wne
    #
    @42
    @44
    wceq
    @19
    @45
    @2
    @23
    @10
    @13
    c0
    eldifsni
    ad2antlr
    #
    vz
    @10
    cA
    @25
    iinin1
    syl
    @41
    @5
    cvv
    wcel
    #
    @1
    @43
    @5
    wcel
    @44
    @6
    wcel
    @47
    @41
    cJ
    cfi
    fvex
    #
    a1i
    @0
    @1
    @19
    @23
    simpllr
    @41
    @43
    @22
    crn
    cint
    #
    @5
    @41
    @22
    @10
    wfn
    #
    @43
    @49
    wceq
    @23
    @50
    @20
    @10
    cJ
    @22
    ffn
    adantl
    vz
    @10
    @22
    fniinfv
    syl
    @41
    @0
    @23
    @45
    @31
    @49
    @5
    wcel
    @0
    @1
    @19
    @23
    simplll
    @20
    @23
    simpr
    @46
    @20
    @31
    @23
    @39
    adantr
    @10
    cJ
    @22
    cvv
    intrnfi
    syl13anc
    eqeltrd
    @43
    cA
    @5
    cvv
    cvv
    elrestr
    syl3anc
    eqeltrd
    @28
    @11
    @42
    @6
    @28
    @11
    vz
    @10
    @24
    ciin
    #
    @42
    vz
    @10
    intiin
    #
    vz
    @10
    @24
    @26
    iineq2
    syl5eq
    eleq1d
    syl5ibrcom
    expimpd
    exlimdv
    mpd
    @7
    @11
    @6
    eleq1
    syl5ibrcom
    rexlimdva
    syl5bi
    @2
    @9
    @7
    @24
    cA
    cin
    #
    wceq
    #
    vz
    @5
    wrex
    #
    @8
    @2
    @47
    @1
    @9
    @55
    wb
    @48
    @0
    @1
    simpr
    vz
    @7
    cA
    @5
    cvv
    cvv
    elrest
    sylancr
    @2
    @54
    @8
    vz
    @5
    @2
    @24
    @5
    wcel
    #
    @24
    @11
    wceq
    #
    vy
    cJ
    cpw
    cfn
    cin
    #
    @14
    cdif
    #
    wrex
    #
    @54
    @8
    wi
    #
    @0
    @56
    @60
    wb
    @1
    vy
    @24
    cJ
    cvv
    elfi2
    adantr
    @2
    @57
    @61
    vy
    @59
    @2
    @10
    @59
    wcel
    #
    wa
    #
    @61
    @57
    @7
    @11
    cA
    cin
    #
    wceq
    #
    @8
    wi
    @63
    @8
    @65
    @64
    @4
    wcel
    @63
    vz
    @10
    @53
    ciin
    #
    @64
    @4
    @63
    @66
    @51
    cA
    cin
    #
    @64
    @63
    @45
    @66
    @67
    wceq
    @62
    @45
    @2
    @10
    @58
    c0
    eldifsni
    adantl
    #
    vz
    @10
    cA
    @24
    iinin1
    syl
    @11
    @51
    cA
    @52
    ineq1i
    syl6eqr
    @63
    @17
    @53
    @3
    wcel
    #
    vz
    @10
    wral
    #
    @45
    @31
    @66
    @4
    wcel
    @17
    @63
    @18
    a1i
    @63
    @10
    cJ
    wss
    #
    @69
    vz
    cJ
    wral
    #
    @70
    @63
    @10
    @58
    wcel
    #
    @71
    @62
    @73
    @2
    @10
    @58
    @14
    eldifi
    adantl
    #
    @73
    @71
    @31
    @10
    cJ
    elfpw
    #
    simplbi
    syl
    @2
    @72
    @62
    @2
    @69
    vz
    cJ
    @0
    @1
    @24
    cJ
    wcel
    @69
    @24
    cA
    cJ
    cvv
    cvv
    elrestr
    3expa
    ralrimiva
    adantr
    @69
    vz
    @10
    cJ
    ssralv
    sylc
    @68
    @63
    @73
    @31
    @74
    @73
    @71
    @31
    @75
    simprbi
    syl
    vz
    @10
    @53
    @3
    cvv
    iinfi
    syl13anc
    eqeltrrd
    @7
    @64
    @4
    eleq1
    syl5ibrcom
    @57
    @54
    @65
    @8
    @57
    @53
    @64
    @7
    @24
    @11
    cA
    ineq1
    eqeq2d
    imbi1d
    syl5ibrcom
    rexlimdva
    sylbid
    rexlimdv
    sylbid
    impbid
    eqrdv
    @2
    wn
    #
    c0
    cfi
    cfv
    c0
    @4
    @6
    fi0
    @76
    @3
    c0
    cfi
    cJ
    cA
    crest
    crest
    cdm
    #
    wrel
    cvv
    cvv
    cxp
    #
    wrel
    cvv
    cvv
    relxp
    @77
    @78
    crest
    @78
    wfn
    @77
    @78
    wceq
    restfn
    @78
    crest
    fndm
    ax-mp
    releqi
    mpbir
    #
    ovprc
    fveq2d
    @76
    @0
    wn
    #
    @1
    wn
    #
    wo
    @6
    c0
    wceq
    #
    @0
    @1
    ianor
    @80
    @82
    @81
    @80
    @6
    c0
    cA
    crest
    co
    c0
    @80
    @5
    c0
    cA
    crest
    cJ
    cfi
    fvprc
    oveq1d
    cA
    0rest
    syl6eq
    @5
    cA
    crest
    @79
    ovprc2
    jaoi
    sylbi
    3eqtr4a
    pm2.61i
end
