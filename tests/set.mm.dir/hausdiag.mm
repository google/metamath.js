include "cha.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "ctx.mm"
include "co.mm"
include "ccld.mm"
include "cfv.mm"
include "ishaus.mm"
include "cuni.mm"
include "cdif.mm"
include "cxp.mm"
include "wss.mm"
include "wb.mm"
include "txtop.mm"
include "anidms.mm"
include "wf1o.mm"
include "wf.mm"
include "f1oi.mm"
include "f1of.mm"
include "fssxp.mm"
include "mp2b.mm"
include "txuni.mm"
include "syl5sseq.mm"
include "eqid.mm"
include "iscld2.mm"
include "syl2anc.mm"
include "eltx.mm"
include "cop.mm"
include "wn.mm"
include "eldif.mm"
include "eqcomd.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "imbi1d.mm"
include "impexp.mm"
include "syl6bb.mm"
include "ralbidv2.mm"
include "eleq1.mm"
include "notbid.mm"
include "2rexbidv.mm"
include "imbi12d.mm"
include "ralxp.mm"
include "vex.mm"
include "opelres.mm"
include "wbr.mm"
include "df-br.mm"
include "ideq.mm"
include "bitr3i.mm"
include "iba.mm"
include "adantr.mm"
include "syl5rbbr.mm"
include "adantl.mm"
include "necon3bbid.mm"
include "elssuni.mm"
include "xpss12.mm"
include "syl2an.mm"
include "xpeq12i.mm"
include "syl6sseqr.mm"
include "ad2antrr.mm"
include "sseqtrd.mm"
include "reldisj.mm"
include "syl.mm"
include "cvv.mm"
include "df-res.mm"
include "ineq2i.mm"
include "inass.mm"
include "inss1.mm"
include "syl5ss.mm"
include "ssv.mm"
include "xpss2.mm"
include "ax-mp.mm"
include "syl6ss.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eqr.mm"
include "syl5eq.mm"
include "eqeq1d.mm"
include "wal.mm"
include "opelxp.mm"
include "elin.mm"
include "3bitr4i.mm"
include "notbii.mm"
include "albii.mm"
include "intirr.mm"
include "eq0.mm"
include "bitr3d.mm"
include "anbi2d.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "3bitr4g.mm"
include "2rexbidva.mm"
include "2ralbidva.mm"
include "bitrd.mm"
include "3bitrrd.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem hausdiag
  let cJ: class J
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  assume hausdiag.x: |- X = U. J


  assert |- ( J e. Haus <-> ( J e. Top /\ ( _I |` X ) e. ( Clsd ` ( J tX J ) ) ) )

  proof
    cJ
    cha
    wcel
    cJ
    ctop
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    @1
    vc
    cv
    #
    wcel
    #
    @2
    vd
    cv
    #
    wcel
    #
    @4
    @6
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vd
    cJ
    wrex
    vc
    cJ
    wrex
    #
    wi
    #
    vb
    cX
    wral
    va
    cX
    wral
    #
    wa
    @0
    cid
    cX
    cres
    #
    cJ
    cJ
    ctx
    co
    #
    ccld
    cfv
    wcel
    #
    wa
    va
    vb
    vd
    vc
    cJ
    cX
    hausdiag.x
    ishaus
    @0
    @13
    @16
    @0
    @16
    @15
    cuni
    #
    @14
    cdif
    #
    @15
    wcel
    #
    ve
    cv
    #
    @4
    @6
    cxp
    #
    wcel
    #
    @21
    @18
    wss
    #
    wa
    #
    vd
    cJ
    wrex
    vc
    cJ
    wrex
    #
    ve
    @18
    wral
    #
    @13
    @0
    @15
    ctop
    wcel
    #
    @14
    @17
    wss
    @16
    @19
    wb
    @0
    @27
    cJ
    cJ
    txtop
    anidms
    @0
    cX
    cX
    cxp
    #
    @14
    @17
    cX
    cX
    @14
    wf1o
    cX
    cX
    @14
    wf
    @14
    @28
    wss
    cX
    f1oi
    cX
    cX
    @14
    f1of
    cX
    cX
    @14
    fssxp
    mp2b
    @0
    @28
    @17
    wceq
    #
    cJ
    cJ
    cX
    cX
    hausdiag.x
    hausdiag.x
    txuni
    anidms
    #
    syl5sseq
    @14
    @15
    @17
    @17
    eqid
    iscld2
    syl2anc
    @0
    @19
    @26
    wb
    vc
    vd
    @18
    cJ
    cJ
    ctop
    ctop
    ve
    eltx
    anidms
    @0
    @26
    @1
    @2
    cop
    #
    @14
    wcel
    #
    wn
    #
    @31
    @21
    wcel
    #
    @23
    wa
    #
    vd
    cJ
    wrex
    vc
    cJ
    wrex
    #
    wi
    #
    vb
    cX
    wral
    va
    cX
    wral
    #
    @13
    @0
    @26
    @20
    @14
    wcel
    #
    wn
    #
    @25
    wi
    #
    ve
    @28
    wral
    @38
    @0
    @25
    @41
    ve
    @18
    @28
    @0
    @20
    @18
    wcel
    #
    @25
    wi
    @20
    @28
    wcel
    #
    @40
    wa
    #
    @25
    wi
    @43
    @41
    wi
    @0
    @42
    @44
    @25
    @42
    @20
    @17
    wcel
    #
    @40
    wa
    @0
    @44
    @20
    @17
    @14
    eldif
    @0
    @45
    @43
    @40
    @0
    @17
    @28
    @20
    @0
    @28
    @17
    @30
    eqcomd
    eleq2d
    anbi1d
    syl5bb
    imbi1d
    @43
    @40
    @25
    impexp
    syl6bb
    ralbidv2
    @41
    @37
    ve
    va
    vb
    cX
    cX
    @20
    @31
    wceq
    #
    @40
    @33
    @25
    @36
    @46
    @39
    @32
    @20
    @31
    @14
    eleq1
    notbid
    @46
    @24
    @35
    vc
    vd
    cJ
    cJ
    @46
    @22
    @34
    @23
    @20
    @31
    @21
    eleq1
    anbi1d
    2rexbidv
    imbi12d
    ralxp
    syl6bb
    @0
    @37
    @12
    va
    vb
    cX
    cX
    @0
    @1
    cX
    wcel
    #
    @2
    cX
    wcel
    #
    wa
    #
    wa
    #
    @33
    @3
    @36
    @11
    @50
    @32
    @1
    @2
    @49
    @32
    @1
    @2
    wceq
    #
    wb
    @0
    @32
    @31
    cid
    wcel
    #
    @47
    wa
    #
    @49
    @51
    @1
    @2
    cid
    cX
    vb
    vex
    #
    opelres
    @51
    @52
    @49
    @53
    @52
    @1
    @2
    cid
    wbr
    @51
    @1
    @2
    cid
    df-br
    @1
    @2
    @54
    ideq
    bitr3i
    @47
    @52
    @53
    wb
    @48
    @47
    @52
    iba
    adantr
    syl5rbbr
    syl5bb
    adantl
    necon3bbid
    @50
    @35
    @10
    vc
    vd
    cJ
    cJ
    @50
    @4
    cJ
    wcel
    #
    @6
    cJ
    wcel
    #
    wa
    #
    wa
    #
    @5
    @7
    wa
    #
    @23
    wa
    @59
    @9
    wa
    @35
    @10
    @58
    @23
    @9
    @59
    @58
    @21
    @14
    cin
    #
    c0
    wceq
    #
    @23
    @9
    @58
    @21
    @17
    wss
    @61
    @23
    wb
    @58
    @21
    @28
    @17
    @57
    @21
    @28
    wss
    @50
    @57
    @21
    cJ
    cuni
    #
    @62
    cxp
    #
    @28
    @55
    @4
    @62
    wss
    @6
    @62
    wss
    @21
    @63
    wss
    @56
    @4
    cJ
    elssuni
    @6
    cJ
    elssuni
    @4
    @62
    @6
    @62
    xpss12
    syl2an
    cX
    @62
    cX
    @62
    hausdiag.x
    hausdiag.x
    xpeq12i
    syl6sseqr
    adantl
    #
    @0
    @29
    @49
    @57
    @30
    ad2antrr
    sseqtrd
    @21
    @14
    @17
    reldisj
    syl
    @58
    @61
    @21
    cid
    cin
    #
    c0
    wceq
    #
    @9
    @58
    @60
    @65
    c0
    @58
    @60
    @21
    cid
    cX
    cvv
    cxp
    #
    cin
    #
    cin
    #
    @65
    @14
    @68
    @21
    cid
    cX
    df-res
    ineq2i
    @58
    @69
    @65
    @67
    cin
    #
    @65
    @21
    cid
    @67
    inass
    @58
    @65
    @67
    wss
    @70
    @65
    wceq
    @58
    @65
    @28
    @67
    @58
    @65
    @21
    @28
    @21
    cid
    inss1
    @64
    syl5ss
    cX
    cvv
    wss
    @28
    @67
    wss
    cX
    ssv
    cX
    cvv
    cX
    xpss2
    ax-mp
    syl6ss
    @65
    @67
    df-ss
    sylib
    syl5eqr
    syl5eq
    eqeq1d
    @1
    @1
    @21
    wbr
    #
    wn
    #
    va
    wal
    @1
    @8
    wcel
    #
    wn
    #
    va
    wal
    @66
    @9
    @72
    @74
    va
    @71
    @73
    @1
    @1
    cop
    @21
    wcel
    @5
    @1
    @6
    wcel
    wa
    @71
    @73
    @1
    @1
    @4
    @6
    opelxp
    @1
    @1
    @21
    df-br
    @1
    @4
    @6
    elin
    3bitr4i
    notbii
    albii
    va
    @21
    intirr
    va
    @8
    eq0
    3bitr4i
    syl6bb
    bitr3d
    anbi2d
    @34
    @59
    @23
    @1
    @2
    @4
    @6
    opelxp
    anbi1i
    @5
    @7
    @9
    df-3an
    3bitr4g
    2rexbidva
    imbi12d
    2ralbidva
    bitrd
    3bitrrd
    pm5.32i
    bitri
end
