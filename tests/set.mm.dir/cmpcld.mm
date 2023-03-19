include "ccmp.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "cuni.mm"
include "wss.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "selpw.mm"
include "w3a.mm"
include "wceq.mm"
include "cdif.mm"
include "csn.mm"
include "cun.mm"
include "simp1l.mm"
include "simp2.mm"
include "eqid.mm"
include "cldopn.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "snssd.mm"
include "unssd.mm"
include "simp3.mm"
include "uniss.mm"
include "3ad2ant2.mm"
include "sstrd.mm"
include "undif.mm"
include "sylib.mm"
include "unss1.mm"
include "3ad2ant3.mm"
include "eqsstr3d.mm"
include "difss.mm"
include "unss.mm"
include "sylanblc.mm"
include "eqssd.mm"
include "cvv.mm"
include "uniexg.mm"
include "ad2antrr.mm"
include "3adant3.mm"
include "difexg.mm"
include "unisng.mm"
include "3syl.mm"
include "uneq2d.mm"
include "eqtr4d.mm"
include "uniun.mm"
include "syl6eqr.mm"
include "cmpcov.mm"
include "syl3anc.mm"
include "elfpw.mm"
include "simp2l.mm"
include "uncom.mm"
include "syl6sseq.mm"
include "ssundif.mm"
include "diffi.mm"
include "ad2antll.mm"
include "sylanbrc.mm"
include "wex.mm"
include "sseqtrd.mm"
include "sselda.mm"
include "eluni.mm"
include "simpl.mm"
include "a1i.mm"
include "wn.mm"
include "simpr.mm"
include "elndif.mm"
include "ad2antlr.mm"
include "eleq2.mm"
include "biimpd.mm"
include "com23.mm"
include "imp.mm"
include "mtod.mm"
include "ex.mm"
include "adantrd.mm"
include "velsn.mm"
include "notbii.mm"
include "syl6ibr.mm"
include "jcad.mm"
include "eldif.mm"
include "eximdv.mm"
include "mpd.mm"
include "ssrdv.mm"
include "unieq.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "syl3an2b.mm"
include "rexlimdv3a.mm"
include "3exp.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "ctop.mm"
include "wb.mm"
include "cmptop.mm"
include "cldss.mm"
include "cmpsub.mm"
include "syl2an.mm"
include "mpbird.mm"

theorem cmpcld
  let cS: class S
  let cJ: class J
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w


  assert |- ( ( J e. Comp /\ S e. ( Clsd ` J ) ) -> ( J |`t S ) e. Comp )

  proof
    cJ
    ccmp
    wcel
    #
    cS
    cJ
    ccld
    cfv
    wcel
    #
    wa
    #
    cJ
    cS
    crest
    co
    ccmp
    wcel
    #
    cS
    vs
    cv
    #
    cuni
    #
    wss
    #
    cS
    vt
    cv
    #
    cuni
    #
    wss
    #
    vt
    @4
    cpw
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vs
    cJ
    cpw
    #
    wral
    #
    @2
    @12
    vs
    @13
    @4
    @13
    wcel
    @4
    cJ
    wss
    #
    @2
    @12
    vs
    cJ
    selpw
    @2
    @15
    @6
    @11
    @2
    @15
    @6
    w3a
    #
    cJ
    cuni
    #
    vu
    cv
    #
    cuni
    #
    wceq
    #
    vu
    @4
    @17
    cS
    cdif
    #
    csn
    #
    cun
    #
    cpw
    cfn
    cin
    #
    wrex
    #
    @11
    @16
    @0
    @23
    cJ
    wss
    @17
    @23
    cuni
    #
    wceq
    @25
    @0
    @1
    @15
    @6
    simp1l
    @16
    @4
    @22
    cJ
    @2
    @15
    @6
    simp2
    @16
    @21
    cJ
    @2
    @15
    @21
    cJ
    wcel
    #
    @6
    @1
    @27
    @0
    cS
    cJ
    @17
    @17
    eqid
    #
    cldopn
    adantl
    3ad2ant1
    snssd
    unssd
    @16
    @17
    @5
    @22
    cuni
    #
    cun
    #
    @26
    @16
    @17
    @5
    @21
    cun
    #
    @30
    @16
    @17
    @31
    @16
    @17
    cS
    @21
    cun
    #
    @31
    @16
    cS
    @17
    wss
    #
    @32
    @17
    wceq
    @16
    cS
    @5
    @17
    @2
    @15
    @6
    simp3
    #
    @15
    @2
    @5
    @17
    wss
    #
    @6
    @4
    cJ
    uniss
    3ad2ant2
    #
    sstrd
    cS
    @17
    undif
    sylib
    @6
    @2
    @32
    @31
    wss
    @15
    cS
    @5
    @21
    unss1
    3ad2ant3
    eqsstr3d
    @16
    @35
    @21
    @17
    wss
    @31
    @17
    wss
    @36
    @17
    cS
    difss
    @5
    @21
    @17
    unss
    sylanblc
    eqssd
    @16
    @29
    @21
    @5
    @16
    @17
    cvv
    wcel
    #
    @21
    cvv
    wcel
    @29
    @21
    wceq
    @2
    @15
    @37
    @6
    @0
    @37
    @1
    @15
    cJ
    ccmp
    uniexg
    ad2antrr
    3adant3
    @17
    cS
    cvv
    difexg
    @21
    cvv
    unisng
    3syl
    uneq2d
    eqtr4d
    @4
    @22
    uniun
    syl6eqr
    @23
    cJ
    @17
    vu
    @28
    cmpcov
    syl3anc
    @16
    @20
    @11
    vu
    @24
    @18
    @24
    wcel
    @16
    @18
    @23
    wss
    #
    @18
    cfn
    wcel
    #
    wa
    #
    @20
    @11
    @18
    @23
    elfpw
    @16
    @40
    @20
    w3a
    #
    @18
    @22
    cdif
    #
    @10
    wcel
    #
    cS
    @42
    cuni
    #
    wss
    #
    @11
    @41
    @42
    @4
    wss
    #
    @42
    cfn
    wcel
    #
    @43
    @41
    @18
    @22
    @4
    cun
    #
    wss
    @46
    @41
    @18
    @23
    @48
    @16
    @38
    @39
    @20
    simp2l
    @4
    @22
    uncom
    syl6sseq
    @18
    @22
    @4
    ssundif
    sylib
    @16
    @40
    @47
    @20
    @39
    @47
    @16
    @38
    @18
    @22
    diffi
    ad2antll
    3adant3
    @42
    @4
    elfpw
    sylanbrc
    @41
    vv
    cS
    @44
    @41
    vv
    cv
    #
    cS
    wcel
    #
    @49
    vw
    cv
    #
    wcel
    #
    @51
    @42
    wcel
    #
    wa
    #
    vw
    wex
    #
    @49
    @44
    wcel
    @41
    @50
    @55
    @41
    @50
    wa
    #
    @52
    @51
    @18
    wcel
    #
    wa
    #
    vw
    wex
    #
    @55
    @56
    @49
    @19
    wcel
    @59
    @41
    cS
    @19
    @49
    @41
    cS
    @5
    @19
    @16
    @40
    @6
    @20
    @34
    3ad2ant1
    @41
    @5
    @17
    @19
    @16
    @40
    @35
    @20
    @36
    3ad2ant1
    @16
    @40
    @20
    simp3
    sseqtrd
    sstrd
    sselda
    vw
    @49
    @18
    eluni
    sylib
    @56
    @58
    @54
    vw
    @56
    @58
    @52
    @53
    @58
    @52
    wi
    @56
    @52
    @57
    simpl
    a1i
    @56
    @58
    @57
    @51
    @22
    wcel
    #
    wn
    #
    wa
    @53
    @56
    @58
    @57
    @61
    @58
    @57
    wi
    @56
    @52
    @57
    simpr
    a1i
    @56
    @58
    @51
    @21
    wceq
    #
    wn
    #
    @61
    @56
    @52
    @63
    @57
    @56
    @52
    @63
    @56
    @52
    wa
    @62
    @49
    @21
    wcel
    #
    @50
    @64
    wn
    @41
    @52
    @49
    cS
    @17
    elndif
    ad2antlr
    @56
    @52
    @62
    @64
    wi
    @56
    @62
    @52
    @64
    @62
    @52
    @64
    wi
    wi
    @56
    @62
    @52
    @64
    @51
    @21
    @49
    eleq2
    biimpd
    a1i
    com23
    imp
    mtod
    ex
    adantrd
    @60
    @62
    vw
    @21
    velsn
    notbii
    syl6ibr
    jcad
    @51
    @18
    @22
    eldif
    syl6ibr
    jcad
    eximdv
    mpd
    ex
    vw
    @49
    @42
    eluni
    syl6ibr
    ssrdv
    @9
    @45
    vt
    @42
    @10
    @7
    @42
    wceq
    @8
    @44
    cS
    @7
    @42
    unieq
    sseq2d
    rspcev
    syl2anc
    syl3an2b
    rexlimdv3a
    mpd
    3exp
    syl5bi
    ralrimiv
    @0
    cJ
    ctop
    wcel
    @33
    @3
    @14
    wb
    @1
    cJ
    cmptop
    cS
    cJ
    @17
    @28
    cldss
    cS
    cJ
    @17
    vs
    vt
    @28
    cmpsub
    syl2an
    mpbird
end
