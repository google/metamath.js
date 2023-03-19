include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cn0v.mm"
include "cfv.mm"
include "cba.mm"
include "ccnp.mm"
include "cnv.mm"
include "eqid.mm"
include "nvzcl.mm"
include "ax-mp.mm"
include "cxmt.mm"
include "ctopon.mm"
include "cme.mm"
include "imsmet.mm"
include "metxmet.mm"
include "mopntopon.mm"
include "toponunii.mm"
include "cncnpi.mm"
include "mpan2.mm"
include "blocnilem.mm"
include "sylancr.mm"
include "c0o.mm"
include "eleq1.mm"
include "wne.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cnmoo.mm"
include "cdiv.mm"
include "simprr.mm"
include "cr.mm"
include "cc0.mm"
include "nmblore.mm"
include "mp3an12.mm"
include "wb.mm"
include "nmlnogt0.mm"
include "mp3an.mm"
include "biimpi.mm"
include "anim12i.mm"
include "elrp.mm"
include "sylibr.mm"
include "adantr.mm"
include "rpdivcld.mm"
include "cmul.mm"
include "simprl.mm"
include "metcl.mm"
include "mp3an1.mm"
include "sylan.mm"
include "simplrr.mm"
include "rpred.mm"
include "ad2antrr.mm"
include "ltmuldiv2.mm"
include "syl3anc.mm"
include "cle.mm"
include "id.mm"
include "ad2ant2r.mm"
include "blometi.mm"
include "3expa.mm"
include "lnof.mm"
include "ffvelrni.mm"
include "syl2an.mm"
include "remulcl.mm"
include "anassrs.mm"
include "adantllr.mm"
include "adantlrr.mm"
include "lelttr.mm"
include "mpand.mm"
include "sylbird.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ralrimivva.mm"
include "jctil.mm"
include "metcn.mm"
include "mp2an.mm"
include "csn.mm"
include "cxp.mm"
include "0ofval.mm"
include "cnconst2.mm"
include "eqeltri.mm"
include "a1i.mm"
include "pm2.61ne.mm"
include "impbii.mm"

theorem blocni
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cU: class U
  let cJ: class J
  let cK: class K
  let cL: class L
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cX: class X
  assume blocni.8: |- C = ( IndMet ` U )
  assume blocni.d: |- D = ( IndMet ` W )
  assume blocni.j: |- J = ( MetOpen ` C )
  assume blocni.k: |- K = ( MetOpen ` D )
  assume blocni.4: |- L = ( U LnOp W )
  assume blocni.5: |- B = ( U BLnOp W )
  assume blocni.u: |- U e. NrmCVec
  assume blocni.w: |- W e. NrmCVec
  assume blocni.l: |- T e. L


  assert |- ( T e. ( J Cn K ) <-> T e. B )

  proof
    cT
    cJ
    cK
    ccn
    co
    #
    wcel
    #
    cT
    cB
    wcel
    #
    @1
    cU
    cn0v
    cfv
    #
    cU
    cba
    cfv
    #
    wcel
    #
    cT
    @3
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    @2
    cU
    cnv
    wcel
    #
    @5
    blocni.u
    cU
    @4
    @3
    @4
    eqid
    #
    @3
    eqid
    nvzcl
    ax-mp
    #
    @1
    @5
    @6
    @9
    @3
    cT
    cJ
    cK
    @4
    @4
    cJ
    cC
    @4
    cxmt
    cfv
    wcel
    #
    cJ
    @4
    ctopon
    cfv
    wcel
    #
    cC
    @4
    cme
    cfv
    wcel
    #
    @10
    @7
    @12
    blocni.u
    cC
    cU
    @4
    @8
    blocni.8
    imsmet
    ax-mp
    #
    cC
    @4
    metxmet
    ax-mp
    #
    cC
    cJ
    @4
    blocni.j
    mopntopon
    ax-mp
    #
    toponunii
    cncnpi
    mpan2
    cB
    cC
    cD
    @3
    cT
    cU
    cJ
    cK
    cL
    cW
    @4
    blocni.8
    blocni.d
    blocni.j
    blocni.k
    blocni.4
    blocni.5
    blocni.u
    blocni.w
    blocni.l
    @8
    blocnilem
    sylancr
    @2
    @1
    cU
    cW
    c0o
    co
    #
    @0
    wcel
    #
    cT
    @16
    cT
    @16
    @0
    eleq1
    @2
    cT
    @16
    wne
    #
    wa
    #
    @4
    cW
    cba
    cfv
    #
    cT
    wf
    #
    vx
    cv
    #
    vw
    cv
    #
    cC
    co
    #
    vz
    cv
    #
    clt
    wbr
    #
    @22
    cT
    cfv
    #
    @23
    cT
    cfv
    #
    cD
    co
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    @4
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    vx
    @4
    wral
    #
    wa
    #
    @1
    @19
    @35
    @21
    @19
    @34
    vx
    vy
    @4
    crp
    @19
    @22
    @4
    wcel
    #
    @30
    crp
    wcel
    #
    wa
    #
    wa
    #
    @30
    cT
    cU
    cW
    cnmoo
    co
    #
    cfv
    #
    cdiv
    co
    #
    crp
    wcel
    @24
    @43
    clt
    wbr
    #
    @31
    wi
    #
    vw
    @4
    wral
    #
    @34
    @40
    @30
    @42
    @19
    @37
    @38
    simprr
    @19
    @42
    crp
    wcel
    #
    @39
    @19
    @42
    cr
    wcel
    #
    cc0
    @42
    clt
    wbr
    #
    wa
    #
    @47
    @2
    @48
    @18
    @49
    @7
    cW
    cnv
    wcel
    #
    @2
    @48
    blocni.u
    blocni.w
    cB
    cT
    cU
    @41
    cW
    @4
    @20
    @8
    @20
    eqid
    #
    @41
    eqid
    #
    blocni.5
    nmblore
    mp3an12
    #
    @18
    @49
    @7
    @51
    cT
    cL
    wcel
    #
    @18
    @49
    wb
    blocni.u
    blocni.w
    blocni.l
    cT
    cU
    cL
    @41
    cW
    @16
    @53
    @16
    eqid
    #
    blocni.4
    nmlnogt0
    mp3an
    biimpi
    anim12i
    #
    @42
    elrp
    sylibr
    adantr
    rpdivcld
    @40
    @45
    vw
    @4
    @40
    @23
    @4
    wcel
    #
    wa
    #
    @44
    @42
    @24
    cmul
    co
    #
    @30
    clt
    wbr
    #
    @31
    @59
    @24
    cr
    wcel
    #
    @30
    cr
    wcel
    #
    @50
    @61
    @44
    wb
    @40
    @37
    @58
    @62
    @19
    @37
    @38
    simprl
    #
    @12
    @37
    @58
    @62
    @13
    @22
    @23
    cC
    @4
    metcl
    mp3an1
    #
    sylan
    @59
    @30
    @19
    @37
    @38
    @58
    simplrr
    rpred
    #
    @19
    @50
    @39
    @58
    @57
    ad2antrr
    @24
    @30
    @42
    ltmuldiv2
    syl3anc
    @59
    @29
    @60
    cle
    wbr
    #
    @61
    @31
    @40
    @2
    @37
    wa
    #
    @58
    @67
    @2
    @37
    @68
    @18
    @38
    @68
    id
    ad2ant2r
    @2
    @37
    @58
    @67
    cB
    cC
    cD
    @22
    @23
    cT
    cU
    @41
    cW
    @4
    @20
    @8
    @52
    blocni.8
    blocni.d
    @53
    blocni.5
    blocni.u
    blocni.w
    blometi
    3expa
    sylan
    @59
    @29
    cr
    wcel
    #
    @60
    cr
    wcel
    #
    @63
    @67
    @61
    wa
    @31
    wi
    @40
    @37
    @58
    @69
    @64
    @37
    @27
    @20
    wcel
    #
    @28
    @20
    wcel
    #
    @69
    @58
    @4
    @20
    @22
    cT
    @7
    @51
    @55
    @21
    blocni.u
    blocni.w
    blocni.l
    cT
    cU
    cL
    cW
    @4
    @20
    @8
    @52
    blocni.4
    lnof
    mp3an
    #
    ffvelrni
    @4
    @20
    @23
    cT
    @73
    ffvelrni
    cD
    @20
    cme
    cfv
    wcel
    #
    @71
    @72
    @69
    @51
    @74
    blocni.w
    cD
    cW
    @20
    @52
    blocni.d
    imsmet
    ax-mp
    #
    @27
    @28
    cD
    @20
    metcl
    mp3an1
    syl2an
    sylan
    @19
    @37
    @58
    @70
    @38
    @2
    @37
    @58
    @70
    @18
    @2
    @37
    @58
    @70
    @2
    @48
    @62
    @70
    @37
    @58
    wa
    @54
    @65
    @42
    @24
    remulcl
    syl2an
    anassrs
    adantllr
    adantlrr
    @66
    @29
    @60
    @30
    lelttr
    syl3anc
    mpand
    sylbird
    ralrimiva
    @33
    @46
    vz
    @43
    crp
    @25
    @43
    wceq
    #
    @32
    @45
    vw
    @4
    @76
    @26
    @44
    @31
    @25
    @43
    @24
    clt
    breq2
    imbi1d
    ralbidv
    rspcev
    syl2anc
    ralrimivva
    @73
    jctil
    @10
    cD
    @20
    cxmt
    cfv
    wcel
    #
    @1
    @36
    wb
    @14
    @74
    @77
    @75
    cD
    @20
    metxmet
    ax-mp
    #
    vx
    vy
    vz
    vw
    cC
    cD
    cT
    cJ
    cK
    @4
    @20
    blocni.j
    blocni.k
    metcn
    mp2an
    sylibr
    @17
    @2
    @16
    @4
    cW
    cn0v
    cfv
    #
    csn
    cxp
    #
    @0
    @7
    @51
    @16
    @80
    wceq
    blocni.u
    blocni.w
    cU
    @16
    cW
    @4
    @79
    @8
    @79
    eqid
    #
    @56
    0ofval
    mp2an
    @11
    cK
    @20
    ctopon
    cfv
    wcel
    #
    @79
    @20
    wcel
    #
    @80
    @0
    wcel
    @15
    @77
    @82
    @78
    cD
    cK
    @20
    blocni.k
    mopntopon
    ax-mp
    @51
    @83
    blocni.w
    cW
    @20
    @79
    @52
    @81
    nvzcl
    ax-mp
    @79
    cJ
    cK
    @4
    @20
    cnconst2
    mp3an
    eqeltri
    a1i
    pm2.61ne
    impbii
end
