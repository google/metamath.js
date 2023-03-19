include "cqqh.mm"
include "cfv.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cq.mm"
include "cxp.mm"
include "cres.mm"
include "cmetu.mm"
include "cucn.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cds.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cdr.mm"
include "cchr.mm"
include "cc0.mm"
include "wceq.mm"
include "cdvr.mm"
include "czrh.mm"
include "eqid.mm"
include "qqhf.mm"
include "syl2anc.mm"
include "wa.mm"
include "simpr.mm"
include "csg.mm"
include "cnm.mm"
include "cngp.mm"
include "cnrg.mm"
include "nrgngp.mm"
include "syl.mm"
include "ad2antrr.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "ngpdsr.mm"
include "syl3anc.mm"
include "simplr.mm"
include "ccnfld.mm"
include "csubg.mm"
include "csubrg.mm"
include "cress.mm"
include "qsubdrg.mm"
include "simpli.mm"
include "subrgsubg.mm"
include "ax-mp.mm"
include "cnfldsub.mm"
include "subgsub.mm"
include "mp3an1.mm"
include "fveq2d.mm"
include "cghm.mm"
include "qqhghm.mm"
include "qrngbas.mm"
include "ghmsub.mm"
include "eqtr2d.mm"
include "cin.mm"
include "cnlm.mm"
include "elind.mm"
include "qsubcl.mm"
include "qqhnm.mm"
include "syl31anc.mm"
include "3eqtrd.mm"
include "ovresd.mm"
include "cc.mm"
include "qsscn.mm"
include "sseldi.mm"
include "cnmetdval.mm"
include "abssubd.mm"
include "3eqtr4d.mm"
include "3eqtr4rd.mm"
include "breq1d.mm"
include "biimpd.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "c0.mm"
include "wne.mm"
include "cz.mm"
include "0z.mm"
include "zq.mm"
include "ne0i.mm"
include "mp2b.mm"
include "a1i.mm"
include "crg.mm"
include "cur.mm"
include "drngring.mm"
include "ringidcl.mm"
include "4syl.mm"
include "cxmt.mm"
include "cpsmet.mm"
include "cxme.mm"
include "cvv.mm"
include "cnfldxms.mm"
include "qex.mm"
include "ressxms.mm"
include "mp2an.mm"
include "eqeltri.mm"
include "cnfldds.mm"
include "ressds.mm"
include "xmsxmet2.mm"
include "mp1i.mm"
include "xmetpsmet.mm"
include "ngpxms.mm"
include "metucn.mm"
include "mpbir2and.mm"
include "cuss.mm"
include "crest.mm"
include "fveq2i.mm"
include "ressuss.mm"
include "3eqtri.mm"
include "cnflduss.mm"
include "oveq1i.mm"
include "wss.mm"
include "cnxmet.mm"
include "restmetu.mm"
include "mp3an.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"

theorem qqhucn
  let wph: wff ph
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cV: class V
  let cZ: class Z
  let vd: setvar d
  let ve: setvar e
  let vp: setvar p
  let vq: setvar q
  assume qqhucn.b: |- B = ( Base ` R )
  assume qqhucn.q: |- Q = ( CCfld |`s QQ )
  assume qqhucn.u: |- U = ( UnifSt ` Q )
  assume qqhucn.v: |- V = ( metUnif ` ( ( dist ` R ) |` ( B X. B ) ) )
  assume qqhucn.z: |- Z = ( ZMod ` R )
  assume qqhucn.1: |- ( ph -> R e. NrmRing )
  assume qqhucn.2: |- ( ph -> R e. DivRing )
  assume qqhucn.3: |- ( ph -> Z e. NrmMod )
  assume qqhucn.4: |- ( ph -> ( chr ` R ) = 0 )


  assert |- ( ph -> ( QQHom ` R ) e. ( U uCn V ) )

  proof
    wph
    cR
    cqqh
    cfv
    #
    cabs
    cmin
    ccom
    #
    cq
    cq
    cxp
    #
    cres
    #
    cmetu
    cfv
    #
    cV
    cucn
    co
    #
    cU
    cV
    cucn
    co
    wph
    @0
    @5
    wcel
    cq
    cB
    @0
    wf
    #
    vp
    cv
    #
    vq
    cv
    #
    @3
    co
    #
    vd
    cv
    #
    clt
    wbr
    #
    @7
    @0
    cfv
    #
    @8
    @0
    cfv
    #
    cR
    cds
    cfv
    #
    cB
    cB
    cxp
    cres
    #
    co
    #
    ve
    cv
    #
    clt
    wbr
    #
    wi
    #
    vq
    cq
    wral
    vp
    cq
    wral
    #
    vd
    crp
    wrex
    #
    ve
    crp
    wral
    wph
    cR
    cdr
    wcel
    #
    cR
    cchr
    cfv
    cc0
    wceq
    #
    @6
    qqhucn.2
    qqhucn.4
    cB
    cR
    cdvr
    cfv
    #
    cR
    cR
    czrh
    cfv
    #
    qqhucn.b
    @24
    eqid
    #
    @25
    eqid
    #
    qqhf
    syl2anc
    #
    wph
    @21
    ve
    crp
    wph
    @17
    crp
    wcel
    #
    wa
    @29
    @9
    @17
    clt
    wbr
    #
    @18
    wi
    #
    vq
    cq
    wral
    #
    vp
    cq
    wral
    #
    @21
    wph
    @29
    simpr
    wph
    @33
    @29
    wph
    @32
    vp
    cq
    wph
    @7
    cq
    wcel
    #
    wa
    #
    @31
    vq
    cq
    @35
    @8
    cq
    wcel
    #
    wa
    #
    @30
    @18
    @37
    @9
    @16
    @17
    clt
    @37
    @12
    @13
    @14
    co
    #
    @8
    @7
    cmin
    co
    #
    cabs
    cfv
    #
    @16
    @9
    @37
    @38
    @13
    @12
    cR
    csg
    cfv
    #
    co
    #
    cR
    cnm
    cfv
    #
    cfv
    #
    @39
    @0
    cfv
    #
    @43
    cfv
    #
    @40
    @37
    cR
    cngp
    wcel
    #
    @12
    cB
    wcel
    #
    @13
    cB
    wcel
    @38
    @44
    wceq
    wph
    @47
    @34
    @36
    wph
    cR
    cnrg
    wcel
    #
    @47
    qqhucn.1
    cR
    nrgngp
    #
    syl
    ad2antrr
    @35
    @48
    @36
    wph
    cq
    cB
    @7
    @0
    @28
    ffvelrnda
    adantr
    #
    @35
    cq
    cB
    @8
    @0
    wph
    @6
    @34
    @28
    adantr
    ffvelrnda
    #
    @12
    @13
    @14
    cR
    @41
    @43
    cB
    @43
    eqid
    #
    qqhucn.b
    @41
    eqid
    #
    @14
    eqid
    #
    ngpdsr
    syl3anc
    @37
    @42
    @45
    @43
    @37
    @45
    @8
    @7
    cQ
    csg
    cfv
    #
    co
    #
    @0
    cfv
    #
    @42
    @37
    @39
    @57
    @0
    @37
    @36
    @34
    @39
    @57
    wceq
    #
    @35
    @36
    simpr
    #
    wph
    @34
    @36
    simplr
    #
    cq
    ccnfld
    csubg
    cfv
    wcel
    #
    @36
    @34
    @59
    cq
    ccnfld
    csubrg
    cfv
    wcel
    #
    @62
    @63
    ccnfld
    cq
    cress
    co
    #
    cdr
    wcel
    qsubdrg
    simpli
    cq
    ccnfld
    subrgsubg
    ax-mp
    cq
    ccnfld
    cQ
    cmin
    @56
    @8
    @7
    cnfldsub
    qqhucn.q
    @56
    eqid
    #
    subgsub
    mp3an1
    syl2anc
    fveq2d
    @37
    @0
    cQ
    cR
    cghm
    co
    wcel
    #
    @36
    @34
    @58
    @42
    wceq
    wph
    @66
    @34
    @36
    wph
    @22
    @23
    @66
    qqhucn.2
    qqhucn.4
    cB
    @24
    cQ
    cR
    @25
    qqhucn.b
    @26
    @27
    qqhucn.q
    qqhghm
    syl2anc
    ad2antrr
    @60
    @61
    cq
    cQ
    cR
    @8
    @0
    @56
    @41
    @7
    cQ
    qqhucn.q
    qrngbas
    #
    @65
    @54
    ghmsub
    syl3anc
    eqtr2d
    fveq2d
    @37
    cR
    cnrg
    cdr
    cin
    wcel
    #
    cZ
    cnlm
    wcel
    #
    @23
    @39
    cq
    wcel
    #
    @46
    @40
    wceq
    wph
    @68
    @34
    @36
    wph
    cnrg
    cdr
    cR
    qqhucn.1
    qqhucn.2
    elind
    ad2antrr
    wph
    @69
    @34
    @36
    qqhucn.3
    ad2antrr
    wph
    @23
    @34
    @36
    qqhucn.4
    ad2antrr
    @37
    @36
    @34
    @70
    @60
    @61
    @8
    @7
    qsubcl
    syl2anc
    @39
    cR
    @43
    cZ
    @53
    qqhucn.z
    qqhnm
    syl31anc
    3eqtrd
    @37
    @12
    @13
    @14
    cB
    @51
    @52
    ovresd
    @37
    @7
    @8
    @1
    co
    #
    @7
    @8
    cmin
    co
    cabs
    cfv
    #
    @9
    @40
    @37
    @7
    cc
    wcel
    @8
    cc
    wcel
    @71
    @72
    wceq
    @37
    cq
    cc
    @7
    qsscn
    @61
    sseldi
    #
    @37
    cq
    cc
    @8
    qsscn
    @60
    sseldi
    #
    @7
    @8
    @1
    @1
    eqid
    cnmetdval
    syl2anc
    @37
    @7
    @8
    @1
    cq
    @61
    @60
    ovresd
    @37
    @8
    @7
    @74
    @73
    abssubd
    3eqtr4d
    3eqtr4rd
    breq1d
    biimpd
    ralrimiva
    ralrimiva
    adantr
    @20
    @33
    vd
    @17
    crp
    @10
    @17
    wceq
    #
    @19
    @31
    vp
    vq
    cq
    cq
    @75
    @11
    @30
    @18
    @10
    @17
    @9
    clt
    breq2
    imbi1d
    2ralbidv
    rspcev
    syl2anc
    ralrimiva
    wph
    vp
    vq
    @3
    @15
    @4
    @0
    cV
    cq
    cB
    vd
    ve
    @4
    eqid
    qqhucn.v
    cq
    c0
    wne
    #
    wph
    cc0
    cz
    wcel
    cc0
    cq
    wcel
    @76
    0z
    cc0
    zq
    cq
    cc0
    ne0i
    mp2b
    #
    a1i
    wph
    @22
    cR
    crg
    wcel
    cR
    cur
    cfv
    #
    cB
    wcel
    cB
    c0
    wne
    qqhucn.2
    cR
    drngring
    cB
    cR
    @78
    qqhucn.b
    @78
    eqid
    ringidcl
    cB
    @78
    ne0i
    4syl
    wph
    @3
    cq
    cxmt
    cfv
    wcel
    #
    @3
    cq
    cpsmet
    cfv
    wcel
    cQ
    cxme
    wcel
    @79
    wph
    cQ
    @64
    cxme
    qqhucn.q
    ccnfld
    cxme
    wcel
    cq
    cvv
    wcel
    #
    @64
    cxme
    wcel
    cnfldxms
    qex
    cq
    ccnfld
    cvv
    ressxms
    mp2an
    eqeltri
    @1
    cQ
    cq
    @67
    @80
    @1
    cQ
    cds
    cfv
    wceq
    qex
    cq
    @1
    ccnfld
    cQ
    cvv
    qqhucn.q
    cnfldds
    ressds
    ax-mp
    xmsxmet2
    mp1i
    @3
    cq
    xmetpsmet
    syl
    wph
    @15
    cB
    cxmt
    cfv
    wcel
    #
    @15
    cB
    cpsmet
    cfv
    wcel
    wph
    @49
    @47
    cR
    cxme
    wcel
    @81
    qqhucn.1
    @50
    cR
    ngpxms
    @14
    cR
    cB
    qqhucn.b
    @55
    xmsxmet2
    4syl
    @15
    cB
    xmetpsmet
    syl
    metucn
    mpbir2and
    wph
    cU
    @4
    cV
    cucn
    cU
    @4
    wceq
    wph
    cU
    ccnfld
    cuss
    cfv
    #
    @2
    crest
    co
    #
    @1
    cmetu
    cfv
    #
    @2
    crest
    co
    #
    @4
    cU
    cQ
    cuss
    cfv
    @64
    cuss
    cfv
    #
    @83
    qqhucn.u
    cQ
    @64
    cuss
    qqhucn.q
    fveq2i
    @80
    @86
    @83
    wceq
    qex
    cq
    cvv
    ccnfld
    ressuss
    ax-mp
    3eqtri
    @82
    @84
    @2
    crest
    @82
    @82
    eqid
    cnflduss
    oveq1i
    @76
    @1
    cc
    cpsmet
    cfv
    wcel
    #
    cq
    cc
    wss
    @85
    @4
    wceq
    @77
    @1
    cc
    cxmt
    cfv
    wcel
    @87
    cnxmet
    @1
    cc
    xmetpsmet
    ax-mp
    qsscn
    cq
    @1
    cc
    restmetu
    mp3an
    3eqtri
    a1i
    oveq1d
    eleqtrrd
end
