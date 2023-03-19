include "ccom.mm"
include "cnop.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cno.mm"
include "c1.mm"
include "wi.mm"
include "chil.mm"
include "wf.mm"
include "cxr.mm"
include "wcel.mm"
include "wral.mm"
include "wb.mm"
include "cbo.mm"
include "clo.mm"
include "bdopln.mm"
include "ax-mp.mm"
include "lnopcoi.mm"
include "lnopfi.mm"
include "cr.mm"
include "nmopre.mm"
include "remulcli.mm"
include "rexri.mm"
include "nmopub.mm"
include "mp2an.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "0le0.mm"
include "a1i.mm"
include "ch0o.mm"
include "lnopco0i.mm"
include "nmlnop0iHIL.mm"
include "sylib.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "c0v.mm"
include "ho0val.mm"
include "norm0.mm"
include "syl6eq.mm"
include "sylan9eq.mm"
include "sylan.mm"
include "oveq2.mm"
include "recni.mm"
include "mul01i.mm"
include "adantr.mm"
include "3brtr4d.mm"
include "adantrr.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "cdiv.mm"
include "csm.mm"
include "cabs.mm"
include "cc.mm"
include "ffvelrni.mm"
include "normcl.mm"
include "syl.mm"
include "recnd.mm"
include "divrec2.mm"
include "mp3an2.mm"
include "ancoms.mm"
include "rerecclzi.mm"
include "clt.mm"
include "bdopf.mm"
include "nmopgt0.mm"
include "recgt0i.mm"
include "sylbi.mm"
include "0re.mm"
include "ltle.mm"
include "mpan.mm"
include "sylc.mm"
include "absidd.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "recclzi.mm"
include "norm-iii.mm"
include "syl2an.mm"
include "lnopmuli.mm"
include "hocoi.mm"
include "oveq2d.mm"
include "adantl.mm"
include "hvmulcl.mm"
include "nmoplb.mm"
include "mp3an1.mm"
include "mulid2i.mm"
include "syl6breqr.mm"
include "1red.mm"
include "biimpi.mm"
include "ledivmul2.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "syl2anc.mm"
include "ad2antrl.mm"
include "jctil.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "sylanbr.mm"
include "pm2.61ian.mm"
include "ex.mm"
include "mprgbir.mm"

theorem nmopcoi
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  assume nmoptri.1: |- S e. BndLinOp
  assume nmoptri.2: |- T e. BndLinOp


  assert |- ( normop ` ( S o. T ) ) <_ ( ( normop ` S ) x. ( normop ` T ) )

  proof
    cS
    cT
    ccom
    #
    cnop
    cfv
    #
    cS
    cnop
    cfv
    #
    cT
    cnop
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vx
    cv
    #
    cno
    cfv
    c1
    cle
    wbr
    #
    @6
    @0
    cfv
    #
    cno
    cfv
    #
    @4
    cle
    wbr
    #
    wi
    #
    vx
    chil
    chil
    chil
    @0
    wf
    @4
    cxr
    wcel
    @5
    @11
    vx
    chil
    wral
    wb
    @0
    cS
    cT
    cS
    cbo
    wcel
    #
    cS
    clo
    wcel
    nmoptri.1
    cS
    bdopln
    ax-mp
    #
    cT
    cbo
    wcel
    #
    cT
    clo
    wcel
    nmoptri.2
    cT
    bdopln
    ax-mp
    #
    lnopcoi
    #
    lnopfi
    #
    @4
    @2
    @3
    @12
    @2
    cr
    wcel
    #
    nmoptri.1
    cS
    nmopre
    ax-mp
    #
    @14
    @3
    cr
    wcel
    #
    nmoptri.2
    cT
    nmopre
    ax-mp
    #
    remulcli
    rexri
    vx
    @4
    @0
    nmopub
    mp2an
    @6
    chil
    wcel
    #
    @7
    @10
    @3
    cc0
    wceq
    #
    @22
    @7
    wa
    #
    @10
    @23
    @22
    @10
    @7
    @23
    @22
    wa
    #
    cc0
    cc0
    @9
    @4
    cle
    cc0
    cc0
    cle
    wbr
    @25
    0le0
    a1i
    @23
    @0
    ch0o
    wceq
    #
    @22
    @9
    cc0
    wceq
    @23
    @1
    cc0
    wceq
    @26
    cS
    cT
    @13
    @15
    lnopco0i
    @0
    @16
    nmlnop0iHIL
    sylib
    @26
    @22
    @9
    @6
    ch0o
    cfv
    #
    cno
    cfv
    #
    cc0
    @26
    @8
    @27
    cno
    @6
    @0
    ch0o
    fveq1
    fveq2d
    @22
    @28
    c0v
    cno
    cfv
    cc0
    @22
    @27
    c0v
    cno
    @6
    ho0val
    fveq2d
    norm0
    syl6eq
    sylan9eq
    sylan
    @23
    @4
    cc0
    wceq
    @22
    @23
    @4
    @2
    cc0
    cmul
    co
    cc0
    @3
    cc0
    @2
    cmul
    oveq2
    @2
    @2
    @19
    recni
    mul01i
    syl6eq
    adantr
    3brtr4d
    adantrr
    @23
    wn
    @3
    cc0
    wne
    #
    @24
    @10
    @3
    cc0
    df-ne
    @29
    @24
    wa
    #
    @9
    @3
    cdiv
    co
    #
    @2
    cle
    wbr
    #
    @10
    @30
    @31
    c1
    @3
    cdiv
    co
    #
    @6
    cT
    cfv
    #
    csm
    co
    #
    cS
    cfv
    #
    cno
    cfv
    #
    @2
    cle
    @29
    @22
    @31
    @37
    wceq
    @7
    @29
    @22
    wa
    #
    @31
    @33
    @8
    csm
    co
    #
    cno
    cfv
    #
    @37
    @38
    @31
    @33
    cabs
    cfv
    #
    @9
    cmul
    co
    #
    @40
    @38
    @31
    @33
    @9
    cmul
    co
    #
    @42
    @22
    @29
    @31
    @43
    wceq
    #
    @22
    @9
    cc
    wcel
    #
    @29
    @44
    @22
    @9
    @22
    @8
    chil
    wcel
    #
    @9
    cr
    wcel
    #
    chil
    chil
    @6
    @0
    @17
    ffvelrni
    #
    @8
    normcl
    syl
    #
    recnd
    @45
    @3
    cc
    wcel
    #
    @29
    @44
    @3
    @21
    recni
    #
    @9
    @3
    divrec2
    mp3an2
    sylan
    ancoms
    @38
    @41
    @33
    @9
    cmul
    @29
    @41
    @33
    wceq
    @22
    @29
    @33
    @3
    @21
    rerecclzi
    #
    @29
    @33
    cr
    wcel
    #
    cc0
    @33
    clt
    wbr
    #
    cc0
    @33
    cle
    wbr
    #
    @52
    @29
    cc0
    @3
    clt
    wbr
    #
    @54
    chil
    chil
    cT
    wf
    #
    @29
    @56
    wb
    @14
    @57
    nmoptri.2
    cT
    bdopf
    ax-mp
    #
    cT
    nmopgt0
    ax-mp
    #
    @3
    @21
    recgt0i
    sylbi
    cc0
    cr
    wcel
    @53
    @54
    @55
    wi
    0re
    cc0
    @33
    ltle
    mpan
    sylc
    absidd
    adantr
    #
    oveq1d
    eqtr4d
    @29
    @33
    cc
    wcel
    #
    @46
    @40
    @42
    wceq
    @22
    @3
    @51
    recclzi
    #
    @48
    @33
    @8
    norm-iii
    syl2an
    eqtr4d
    @38
    @36
    @39
    cno
    @38
    @36
    @33
    @34
    cS
    cfv
    #
    csm
    co
    #
    @39
    @29
    @61
    @34
    chil
    wcel
    #
    @36
    @64
    wceq
    @22
    @62
    chil
    chil
    @6
    cT
    @58
    ffvelrni
    #
    @33
    @34
    cS
    @13
    lnopmuli
    syl2an
    @22
    @39
    @64
    wceq
    @29
    @22
    @8
    @63
    @33
    csm
    @6
    cS
    cT
    @12
    chil
    chil
    cS
    wf
    #
    nmoptri.1
    cS
    bdopf
    ax-mp
    #
    @58
    hocoi
    oveq2d
    adantl
    eqtr4d
    fveq2d
    eqtr4d
    adantrr
    @30
    @35
    chil
    wcel
    #
    @35
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    @37
    @2
    cle
    wbr
    #
    @29
    @22
    @69
    @7
    @29
    @61
    @65
    @69
    @22
    @62
    @66
    @33
    @34
    hvmulcl
    syl2an
    adantrr
    @30
    @70
    @34
    cno
    cfv
    #
    @3
    cdiv
    co
    #
    c1
    cle
    @29
    @22
    @70
    @74
    wceq
    @7
    @38
    @70
    @41
    @73
    cmul
    co
    #
    @74
    @29
    @61
    @65
    @70
    @75
    wceq
    @22
    @62
    @66
    @33
    @34
    norm-iii
    syl2an
    @38
    @74
    @33
    @73
    cmul
    co
    #
    @75
    @22
    @29
    @74
    @76
    wceq
    #
    @22
    @73
    cc
    wcel
    #
    @29
    @77
    @22
    @73
    @22
    @65
    @73
    cr
    wcel
    #
    @66
    @34
    normcl
    syl
    #
    recnd
    @78
    @50
    @29
    @77
    @51
    @73
    @3
    divrec2
    mp3an2
    sylan
    ancoms
    @38
    @41
    @33
    @73
    cmul
    @60
    oveq1d
    eqtr4d
    eqtr4d
    adantrr
    @30
    @74
    c1
    cle
    wbr
    #
    @73
    c1
    @3
    cmul
    co
    #
    cle
    wbr
    #
    @24
    @83
    @29
    @24
    @73
    @3
    @82
    cle
    @57
    @22
    @7
    @73
    @3
    cle
    wbr
    @58
    @6
    cT
    nmoplb
    mp3an1
    @3
    @51
    mulid2i
    syl6breqr
    adantl
    @29
    @22
    @81
    @83
    wb
    #
    @7
    @22
    @29
    @84
    @22
    @29
    wa
    #
    @79
    c1
    cr
    wcel
    @20
    @56
    @84
    @22
    @79
    @29
    @80
    adantr
    @85
    1red
    @20
    @85
    @21
    a1i
    @29
    @56
    @22
    @29
    @56
    @59
    biimpi
    #
    adantl
    @73
    c1
    @3
    ledivmul2
    syl112anc
    ancoms
    adantrr
    mpbird
    eqbrtrd
    @67
    @69
    @71
    @72
    @68
    @35
    cS
    nmoplb
    mp3an1
    syl2anc
    eqbrtrd
    @30
    @47
    @18
    @20
    @56
    wa
    @32
    @10
    wb
    @22
    @47
    @29
    @7
    @49
    ad2antrl
    @18
    @30
    @19
    a1i
    @30
    @56
    @20
    @29
    @56
    @24
    @86
    adantr
    @21
    jctil
    @9
    @2
    @3
    ledivmul2
    syl3anc
    mpbid
    sylanbr
    pm2.61ian
    ex
    mprgbir
end
