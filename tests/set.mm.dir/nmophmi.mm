include "cc.mm"
include "wcel.mm"
include "chot.mm"
include "co.mm"
include "cnop.mm"
include "cfv.mm"
include "cabs.mm"
include "cmul.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cno.mm"
include "c1.mm"
include "wi.mm"
include "chil.mm"
include "wral.mm"
include "wa.mm"
include "csm.mm"
include "wf.mm"
include "cbo.mm"
include "bdopf.mm"
include "ax-mp.mm"
include "homval.mm"
include "mp3an2.mm"
include "fveq2d.mm"
include "ffvelrni.mm"
include "norm-iii.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "adantr.mm"
include "cr.mm"
include "cc0.mm"
include "normcl.mm"
include "syl.mm"
include "ad2antlr.mm"
include "abscl.mm"
include "absge0.mm"
include "jca.mm"
include "ad2antrr.mm"
include "nmoplb.mm"
include "mp3an1.mm"
include "adantll.mm"
include "nmopre.mm"
include "lemul2a.mm"
include "mp3anl2.mm"
include "syl21anc.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "ralrimiva.mm"
include "cxr.mm"
include "wb.mm"
include "homulcl.mm"
include "mpan2.mm"
include "remulcl.mm"
include "sylancl.mm"
include "rexrd.mm"
include "nmopub.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "fveq2.mm"
include "abs0.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "recni.mm"
include "mul02i.mm"
include "adantl.mm"
include "nmopge0.mm"
include "wne.mm"
include "cdiv.mm"
include "syl3an1.mm"
include "3expa.mm"
include "eqbrtrrd.mm"
include "adantllr.mm"
include "clt.mm"
include "cmnf.mm"
include "nmopxr.mm"
include "nmopgtmnf.mm"
include "xrre.mm"
include "syl22anc.mm"
include "absgt0.mm"
include "biimpa.mm"
include "lemuldiv2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "abs00.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "redivcld.mm"
include "sylancr.mm"
include "a1i.mm"
include "pm2.61dane.mm"
include "letri3d.mm"
include "mpbir2and.mm"

theorem nmophmi
  let cA: class A
  let cT: class T
  let vx: setvar x
  assume nmophm.1: |- T e. BndLinOp


  assert |- ( A e. CC -> ( normop ` ( A .op T ) ) = ( ( abs ` A ) x. ( normop ` T ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cT
    chot
    co
    #
    cnop
    cfv
    #
    cA
    cabs
    cfv
    #
    cT
    cnop
    cfv
    #
    cmul
    co
    #
    wceq
    @2
    @5
    cle
    wbr
    #
    @5
    @2
    cle
    wbr
    #
    @0
    @6
    vx
    cv
    #
    cno
    cfv
    c1
    cle
    wbr
    #
    @8
    @1
    cfv
    #
    cno
    cfv
    #
    @5
    cle
    wbr
    #
    wi
    #
    vx
    chil
    wral
    #
    @0
    @13
    vx
    chil
    @0
    @8
    chil
    wcel
    #
    wa
    #
    @9
    @12
    @16
    @9
    wa
    #
    @11
    @3
    @8
    cT
    cfv
    #
    cno
    cfv
    #
    cmul
    co
    #
    @5
    cle
    @16
    @11
    @20
    wceq
    @9
    @16
    @11
    cA
    @18
    csm
    co
    #
    cno
    cfv
    #
    @20
    @16
    @10
    @21
    cno
    @0
    chil
    chil
    cT
    wf
    #
    @15
    @10
    @21
    wceq
    cT
    cbo
    wcel
    #
    @23
    nmophm.1
    cT
    bdopf
    ax-mp
    #
    cA
    @8
    cT
    homval
    mp3an2
    fveq2d
    @15
    @0
    @18
    chil
    wcel
    #
    @22
    @20
    wceq
    chil
    chil
    @8
    cT
    @25
    ffvelrni
    #
    cA
    @18
    norm-iii
    sylan2
    eqtrd
    adantr
    #
    @17
    @19
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    wa
    #
    @19
    @4
    cle
    wbr
    #
    @20
    @5
    cle
    wbr
    #
    @15
    @29
    @0
    @9
    @15
    @26
    @29
    @27
    @18
    normcl
    syl
    #
    ad2antlr
    @0
    @32
    @15
    @9
    @0
    @30
    @31
    cA
    abscl
    #
    cA
    absge0
    jca
    ad2antrr
    @15
    @9
    @33
    @0
    @23
    @15
    @9
    @33
    @25
    @8
    cT
    nmoplb
    mp3an1
    adantll
    @29
    @4
    cr
    wcel
    #
    @32
    @33
    @34
    @24
    @37
    nmophm.1
    cT
    nmopre
    ax-mp
    #
    @19
    @4
    @3
    lemul2a
    mp3anl2
    syl21anc
    eqbrtrd
    ex
    ralrimiva
    @0
    chil
    chil
    @1
    wf
    #
    @5
    cxr
    wcel
    @6
    @14
    wb
    @0
    @23
    @39
    @25
    cA
    cT
    homulcl
    mpan2
    #
    @0
    @5
    @0
    @30
    @37
    @5
    cr
    wcel
    #
    @36
    @38
    @3
    @4
    remulcl
    sylancl
    #
    rexrd
    vx
    @5
    @1
    nmopub
    syl2anc
    mpbird
    #
    @0
    @7
    cA
    cc0
    @0
    cA
    cc0
    wceq
    #
    wa
    @5
    cc0
    @2
    cle
    @44
    @5
    cc0
    wceq
    @0
    @44
    @5
    cc0
    @4
    cmul
    co
    cc0
    @44
    @3
    cc0
    @4
    cmul
    @44
    @3
    cc0
    cabs
    cfv
    cc0
    cA
    cc0
    cabs
    fveq2
    abs0
    syl6eq
    oveq1d
    @4
    @4
    @38
    recni
    mul02i
    syl6eq
    adantl
    @0
    cc0
    @2
    cle
    wbr
    #
    @44
    @0
    @39
    @45
    @40
    @1
    nmopge0
    syl
    adantr
    eqbrtrd
    @0
    cA
    cc0
    wne
    #
    wa
    #
    @7
    @4
    @2
    @3
    cdiv
    co
    #
    cle
    wbr
    #
    @47
    @49
    @9
    @19
    @48
    cle
    wbr
    #
    wi
    #
    vx
    chil
    wral
    #
    @47
    @51
    vx
    chil
    @47
    @15
    wa
    #
    @9
    @50
    @53
    @9
    wa
    @20
    @2
    cle
    wbr
    #
    @50
    @0
    @15
    @9
    @54
    @46
    @17
    @11
    @20
    @2
    cle
    @28
    @0
    @15
    @9
    @11
    @2
    cle
    wbr
    #
    @0
    @39
    @15
    @9
    @55
    @40
    @8
    @1
    nmoplb
    syl3an1
    3expa
    eqbrtrrd
    adantllr
    @53
    @54
    @50
    wb
    #
    @9
    @53
    @29
    @2
    cr
    wcel
    #
    @30
    cc0
    @3
    clt
    wbr
    #
    @56
    @15
    @29
    @47
    @35
    adantl
    @0
    @57
    @46
    @15
    @0
    @2
    cxr
    wcel
    #
    @41
    cmnf
    @2
    clt
    wbr
    #
    @6
    @57
    @0
    @39
    @59
    @40
    @1
    nmopxr
    syl
    @42
    @0
    @39
    @60
    @40
    @1
    nmopgtmnf
    syl
    @43
    @2
    @5
    xrre
    syl22anc
    #
    ad2antrr
    @0
    @30
    @46
    @15
    @36
    ad2antrr
    @47
    @58
    @15
    @0
    @46
    @58
    cA
    absgt0
    biimpa
    #
    adantr
    @19
    @2
    @3
    lemuldiv2
    syl112anc
    adantr
    mpbid
    ex
    ralrimiva
    @47
    @23
    @48
    cxr
    wcel
    @49
    @52
    wb
    @25
    @47
    @48
    @47
    @2
    @3
    @0
    @57
    @46
    @61
    adantr
    #
    @0
    @30
    @46
    @36
    adantr
    #
    @0
    @3
    cc0
    wne
    @46
    @0
    @3
    cc0
    cA
    cc0
    cA
    abs00
    necon3bid
    biimpar
    redivcld
    rexrd
    vx
    @48
    cT
    nmopub
    sylancr
    mpbird
    @47
    @37
    @57
    @30
    @58
    @7
    @49
    wb
    @37
    @47
    @38
    a1i
    @63
    @64
    @62
    @4
    @2
    @3
    lemuldiv2
    syl112anc
    mpbird
    pm2.61dane
    @0
    @2
    @5
    @61
    @42
    letri3d
    mpbir2and
end
