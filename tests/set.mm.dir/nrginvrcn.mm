include "cnrg.mm"
include "wcel.mm"
include "cds.mm"
include "cfv.mm"
include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "ccn.mm"
include "co.mm"
include "crest.mm"
include "wf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "crg.mm"
include "cmgp.mm"
include "cress.mm"
include "cgrp.mm"
include "nrgring.mm"
include "eqid.mm"
include "unitgrp.mm"
include "unitgrpbas.mm"
include "invrfval.mm"
include "grpinvf.mm"
include "3syl.mm"
include "wa.mm"
include "cur.mm"
include "c0g.mm"
include "wceq.mm"
include "c0.mm"
include "wne.mm"
include "c1.mm"
include "1rp.mm"
include "ne0ii.mm"
include "ad2antrr.mm"
include "unitss.mm"
include "simplrl.mm"
include "sseldi.mm"
include "simpr.mm"
include "ring1eq0.mm"
include "syl3anc.mm"
include "cc0.mm"
include "cxme.mm"
include "wb.mm"
include "cngp.mm"
include "cmt.mm"
include "nrgngp.mm"
include "ngpms.mm"
include "msxms.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "xmseq0.mm"
include "mpbiri.mm"
include "simplrr.mm"
include "rpgt0d.mm"
include "eqbrtrd.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "breq1d.mm"
include "syl5ibrcom.mm"
include "syld.mm"
include "imp.mm"
include "an32s.mm"
include "a1d.mm"
include "ralrimiva.mm"
include "ralrimivw.mm"
include "r19.2z.mm"
include "sylancr.mm"
include "cnm.mm"
include "cmul.mm"
include "cle.mm"
include "cif.mm"
include "c2.mm"
include "cdiv.mm"
include "simpll.mm"
include "cnzr.mm"
include "isnzr.mm"
include "sylanbrc.mm"
include "nrginvrcnlem.mm"
include "pm2.61dane.mm"
include "ovresd.mm"
include "simpl.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "imbi12d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "ralrimivva.mm"
include "cxmt.mm"
include "wss.mm"
include "xpss12.mm"
include "mp2an.mm"
include "resabs1.mm"
include "ax-mp.mm"
include "xmsxmet.mm"
include "4syl.mm"
include "xmetres2.mm"
include "sylancl.mm"
include "syl5eqelr.mm"
include "metcn.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "mstopn.mm"
include "eqcomi.mm"
include "metrest.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "eleqtrrd.mm"

theorem nrginvrcn
  let cR: class R
  let cU: class U
  let cI: class I
  let cJ: class J
  let cX: class X
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let wph: wff ph
  let cT: class T
  let cA: class A
  let cB: class B
  let cD: class D
  assume nrginvrcn.x: |- X = ( Base ` R )
  assume nrginvrcn.u: |- U = ( Unit ` R )
  assume nrginvrcn.i: |- I = ( invr ` R )
  assume nrginvrcn.j: |- J = ( TopOpen ` R )


  assert |- ( R e. NrmRing -> I e. ( ( J |`t U ) Cn ( J |`t U ) ) )

  proof
    cR
    cnrg
    wcel
    #
    cI
    cR
    cds
    cfv
    #
    cU
    cU
    cxp
    #
    cres
    #
    cmopn
    cfv
    #
    @4
    ccn
    co
    #
    cJ
    cU
    crest
    co
    #
    @6
    ccn
    co
    @0
    cI
    @5
    wcel
    #
    cU
    cU
    cI
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    @3
    co
    #
    vs
    cv
    #
    clt
    wbr
    #
    @9
    cI
    cfv
    #
    @10
    cI
    cfv
    #
    @3
    co
    #
    vr
    cv
    #
    clt
    wbr
    #
    wi
    #
    vy
    cU
    wral
    #
    vs
    crp
    wrex
    #
    vr
    crp
    wral
    vx
    cU
    wral
    #
    @0
    cR
    crg
    wcel
    #
    cR
    cmgp
    cfv
    cU
    cress
    co
    #
    cgrp
    wcel
    @8
    cR
    nrgring
    #
    cR
    cU
    @24
    nrginvrcn.u
    @24
    eqid
    #
    unitgrp
    cU
    @24
    cI
    cR
    cU
    @24
    nrginvrcn.u
    @26
    unitgrpbas
    cR
    cU
    @24
    cI
    nrginvrcn.u
    @26
    nrginvrcn.i
    invrfval
    grpinvf
    3syl
    #
    @0
    @21
    vx
    vr
    cU
    crp
    @0
    @9
    cU
    wcel
    #
    @17
    crp
    wcel
    #
    wa
    #
    wa
    #
    @21
    @9
    @10
    @1
    co
    #
    @12
    clt
    wbr
    #
    @14
    @15
    @1
    co
    #
    @17
    clt
    wbr
    #
    wi
    #
    vy
    cU
    wral
    #
    vs
    crp
    wrex
    #
    @31
    @38
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    @31
    @39
    @40
    wceq
    #
    wa
    #
    crp
    c0
    wne
    @37
    vs
    crp
    wral
    @38
    c1
    crp
    1rp
    ne0ii
    @42
    @37
    vs
    crp
    @42
    @36
    vy
    cU
    @42
    @10
    cU
    wcel
    #
    wa
    @35
    @33
    @31
    @43
    @41
    @35
    @31
    @43
    wa
    #
    @41
    @35
    @44
    @41
    @9
    @10
    wceq
    #
    @35
    @44
    @23
    @9
    cX
    wcel
    @10
    cX
    wcel
    @41
    @45
    wi
    @0
    @23
    @30
    @43
    @25
    ad2antrr
    @44
    cU
    cX
    @9
    cX
    cR
    cU
    nrginvrcn.x
    nrginvrcn.u
    unitss
    #
    @0
    @28
    @29
    @43
    simplrl
    #
    sseldi
    @44
    cU
    cX
    @10
    @46
    @31
    @43
    simpr
    #
    sseldi
    cX
    cR
    @39
    @9
    @10
    @40
    nrginvrcn.x
    @39
    eqid
    #
    @40
    eqid
    #
    ring1eq0
    syl3anc
    @44
    @35
    @45
    @15
    @15
    @1
    co
    #
    @17
    clt
    wbr
    @44
    @51
    cc0
    @17
    clt
    @44
    @51
    cc0
    wceq
    #
    @15
    @15
    wceq
    #
    @15
    eqid
    @44
    cR
    cxme
    wcel
    #
    @15
    cX
    wcel
    #
    @55
    @52
    @53
    wb
    @0
    @54
    @30
    @43
    @0
    cR
    cngp
    wcel
    #
    cR
    cmt
    wcel
    #
    @54
    cR
    nrgngp
    #
    cR
    ngpms
    #
    cR
    msxms
    #
    3syl
    ad2antrr
    @44
    cU
    cX
    @15
    @46
    @31
    cU
    cU
    @10
    cI
    @0
    @8
    @30
    @27
    adantr
    ffvelrnda
    #
    sseldi
    #
    @62
    @15
    @15
    @1
    cR
    cX
    nrginvrcn.x
    @1
    eqid
    #
    xmseq0
    syl3anc
    mpbiri
    @44
    @17
    @0
    @28
    @29
    @43
    simplrr
    rpgt0d
    eqbrtrd
    @45
    @34
    @51
    @17
    clt
    @45
    @14
    @15
    @15
    @1
    @9
    @10
    cI
    fveq2
    oveq1d
    breq1d
    syl5ibrcom
    syld
    imp
    an32s
    a1d
    ralrimiva
    ralrimivw
    @37
    vs
    crp
    r19.2z
    sylancr
    @31
    @39
    @40
    wne
    #
    wa
    #
    vs
    vy
    @9
    @17
    @1
    cR
    c1
    @9
    cR
    cnm
    cfv
    #
    cfv
    #
    @17
    cmul
    co
    #
    cle
    wbr
    c1
    @68
    cif
    @67
    c2
    cdiv
    co
    cmul
    co
    #
    cU
    cI
    @66
    cX
    nrginvrcn.x
    nrginvrcn.u
    nrginvrcn.i
    @66
    eqid
    @63
    @0
    @30
    @64
    simpll
    @65
    @23
    @64
    cR
    cnzr
    wcel
    @0
    @23
    @30
    @64
    @25
    ad2antrr
    @31
    @64
    simpr
    cR
    @39
    @40
    @49
    @50
    isnzr
    sylanbrc
    @0
    @28
    @29
    @64
    simplrl
    @0
    @28
    @29
    @64
    simplrr
    @69
    eqid
    nrginvrcnlem
    pm2.61dane
    @31
    @20
    @37
    vs
    crp
    @31
    @19
    @36
    vy
    cU
    @44
    @13
    @33
    @18
    @35
    @44
    @11
    @32
    @12
    clt
    @44
    @9
    @10
    @1
    cU
    @47
    @48
    ovresd
    breq1d
    @44
    @16
    @34
    @17
    clt
    @44
    @14
    @15
    @1
    cU
    @31
    @14
    cU
    wcel
    #
    @43
    @0
    @8
    @28
    @70
    @30
    @27
    @28
    @29
    simpl
    cU
    cU
    @9
    cI
    ffvelrn
    syl2an
    adantr
    @61
    ovresd
    breq1d
    imbi12d
    ralbidva
    rexbidv
    mpbird
    ralrimivva
    @0
    @3
    cU
    cxmt
    cfv
    #
    wcel
    #
    @72
    @7
    @8
    @22
    wa
    wb
    @0
    @3
    @1
    cX
    cX
    cxp
    #
    cres
    #
    @2
    cres
    #
    @71
    @2
    @73
    wss
    #
    @75
    @3
    wceq
    cU
    cX
    wss
    #
    @77
    @76
    @46
    @46
    cU
    cX
    cU
    cX
    xpss12
    mp2an
    @1
    @2
    @73
    resabs1
    ax-mp
    #
    @0
    @74
    cX
    cxmt
    cfv
    wcel
    #
    @77
    @75
    @71
    wcel
    @0
    @56
    @57
    @54
    @79
    @58
    @59
    @60
    @74
    cR
    cX
    nrginvrcn.x
    @74
    eqid
    #
    xmsxmet
    4syl
    #
    @46
    @74
    cU
    cX
    xmetres2
    sylancl
    syl5eqelr
    #
    @82
    vx
    vr
    vs
    vy
    @3
    @3
    cI
    @4
    @4
    cU
    cU
    @4
    eqid
    #
    @83
    metcn
    syl2anc
    mpbir2and
    @0
    @6
    @4
    @6
    @4
    ccn
    @0
    @6
    @74
    cmopn
    cfv
    #
    cU
    crest
    co
    #
    @4
    @0
    cJ
    @84
    cU
    crest
    @0
    @56
    @57
    cJ
    @84
    wceq
    @58
    @59
    @74
    cJ
    cR
    cX
    nrginvrcn.j
    nrginvrcn.x
    @80
    mstopn
    3syl
    oveq1d
    @0
    @79
    @77
    @85
    @4
    wceq
    @81
    @46
    @74
    @3
    @84
    @4
    cX
    cU
    @75
    @3
    @78
    eqcomi
    @84
    eqid
    @83
    metrest
    sylancl
    eqtrd
    #
    @86
    oveq12d
    eleqtrrd
end
