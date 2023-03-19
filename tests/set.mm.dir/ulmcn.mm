include "cc.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "culm.mm"
include "ulmcl.mm"
include "syl.mm"
include "wa.mm"
include "c2.mm"
include "cdiv.mm"
include "cuz.mm"
include "cz.mm"
include "adantr.mm"
include "cmap.mm"
include "wss.mm"
include "cncff.mm"
include "cvv.mm"
include "wb.mm"
include "cnex.mm"
include "cncfrss.mm"
include "ssexg.mm"
include "sylancl.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"
include "ssriv.mm"
include "fss.mm"
include "eqidd.mm"
include "rphalfcl.mm"
include "ad2antll.mm"
include "rphalfcld.mm"
include "ulmi.mm"
include "r19.2uz.mm"
include "simplrl.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rspcv.mm"
include "ffvelrnda.mm"
include "cncfi.mm"
include "syl3anc.mm"
include "ad2antrr.mm"
include "r19.26.mm"
include "caddc.mm"
include "cr.mm"
include "simplr.mm"
include "ffvelrnd.mm"
include "elmapi.mm"
include "ad3antrrr.mm"
include "subcld.mm"
include "abscld.mm"
include "ffvelrn.mm"
include "sylancom.mm"
include "rpred.mm"
include "lt2add.mm"
include "syl22anc.mm"
include "recnd.mm"
include "2halvesd.mm"
include "breq2d.mm"
include "readdcld.mm"
include "rpre.mm"
include "cle.mm"
include "abs3difd.mm"
include "addcomd.mm"
include "breqtrd.mm"
include "abssubd.mm"
include "oveq1d.mm"
include "leadd2dd.mm"
include "addassd.mm"
include "breqtrrd.mm"
include "letrd.mm"
include "lelttr.mm"
include "mpand.mm"
include "sylbid.mm"
include "syld.mm"
include "expd.mm"
include "expdimp.mm"
include "an32s.mm"
include "imp.mm"
include "imim2d.mm"
include "expimpd.mm"
include "ralimdva.mm"
include "syl5bir.mm"
include "reximdv.mm"
include "mpd.mm"
include "exp31.mm"
include "mpdd.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "ralrimivva.mm"
include "uzid.mm"
include "syl6eleqr.mm"
include "ssid.mm"
include "elcncf2.mm"
include "mpbir2and.mm"

theorem ulmcn
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vw: setvar w
  let vz: setvar z
  let vx: setvar x
  let vy: setvar y
  assume ulmcn.z: |- Z = ( ZZ>= ` M )
  assume ulmcn.m: |- ( ph -> M e. ZZ )
  assume ulmcn.f: |- ( ph -> F : Z --> ( S -cn-> CC ) )
  assume ulmcn.u: |- ( ph -> F ( ~~>u ` S ) G )


  assert |- ( ph -> G e. ( S -cn-> CC ) )

  proof
    wph
    cG
    cS
    cc
    ccncf
    co
    #
    wcel
    #
    cS
    cc
    cG
    wf
    #
    vw
    cv
    #
    vx
    cv
    #
    cmin
    co
    cabs
    cfv
    vz
    cv
    clt
    wbr
    #
    @3
    cG
    cfv
    #
    @4
    cG
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
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
    cS
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
    cS
    wral
    #
    wph
    cF
    cG
    cS
    culm
    cfv
    wbr
    #
    @2
    ulmcn.u
    cS
    cF
    cG
    ulmcl
    syl
    #
    wph
    @14
    vx
    vy
    cS
    crp
    wph
    @4
    cS
    wcel
    #
    @10
    crp
    wcel
    #
    wa
    #
    wa
    #
    @3
    vk
    cv
    #
    cF
    cfv
    #
    cfv
    #
    @6
    cmin
    co
    #
    cabs
    cfv
    #
    @10
    c2
    cdiv
    co
    #
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    vw
    cS
    wral
    #
    vk
    vj
    cv
    cuz
    cfv
    wral
    vj
    cZ
    wrex
    #
    @14
    @21
    vw
    @6
    @24
    @28
    cS
    vj
    vk
    cF
    cG
    cM
    cZ
    ulmcn.z
    wph
    cM
    cz
    wcel
    #
    @20
    ulmcn.m
    adantr
    wph
    cZ
    cc
    cS
    cmap
    co
    #
    cF
    wf
    #
    @20
    wph
    cZ
    @0
    cF
    wf
    #
    @0
    @33
    wss
    @34
    ulmcn.f
    vx
    @0
    @33
    @4
    @0
    wcel
    #
    @4
    @33
    wcel
    #
    cS
    cc
    @4
    wf
    #
    cS
    cc
    @4
    cncff
    @36
    cc
    cvv
    wcel
    #
    cS
    cvv
    wcel
    #
    @37
    @38
    wb
    cnex
    @36
    cS
    cc
    wss
    #
    @39
    @40
    cS
    cc
    @4
    cncfrss
    cnex
    cS
    cc
    cvv
    ssexg
    sylancl
    cc
    cS
    @4
    cvv
    cvv
    elmapg
    sylancr
    mpbird
    ssriv
    cZ
    @0
    @33
    cF
    fss
    sylancl
    adantr
    #
    @21
    @22
    cZ
    wcel
    #
    @3
    cS
    wcel
    #
    wa
    wa
    @24
    eqidd
    @21
    @44
    wa
    @6
    eqidd
    wph
    @16
    @20
    ulmcn.u
    adantr
    @21
    @27
    @19
    @27
    crp
    wcel
    #
    wph
    @18
    @10
    rphalfcl
    ad2antll
    #
    rphalfcld
    ulmi
    @31
    @30
    vk
    cZ
    wrex
    @21
    @14
    @30
    vj
    vk
    cM
    cZ
    ulmcn.z
    r19.2uz
    @21
    @30
    @14
    vk
    cZ
    @21
    @43
    wa
    #
    @30
    @4
    @23
    cfv
    #
    @7
    cmin
    co
    #
    cabs
    cfv
    #
    @28
    clt
    wbr
    #
    @14
    @47
    @18
    @30
    @51
    wi
    wph
    @18
    @19
    @43
    simplrl
    #
    @29
    @51
    vw
    @4
    cS
    vw
    vx
    weq
    #
    @26
    @50
    @28
    clt
    @53
    @25
    @49
    cabs
    @53
    @24
    @48
    @6
    @7
    cmin
    @3
    @4
    @23
    fveq2
    @3
    @4
    cG
    fveq2
    oveq12d
    fveq2d
    breq1d
    rspcv
    syl
    @47
    @30
    @51
    @14
    @47
    @30
    wa
    @51
    wa
    #
    @5
    @24
    @48
    cmin
    co
    #
    cabs
    cfv
    #
    @27
    clt
    wbr
    #
    wi
    #
    vw
    cS
    wral
    #
    vz
    crp
    wrex
    #
    @14
    @47
    @60
    @30
    @51
    @47
    @23
    @0
    wcel
    @18
    @45
    @60
    @21
    cZ
    @0
    @22
    cF
    wph
    @35
    @20
    ulmcn.f
    adantr
    ffvelrnda
    @52
    @21
    @45
    @43
    @46
    adantr
    #
    vz
    vw
    cS
    cc
    @4
    @27
    @23
    cncfi
    syl3anc
    ad2antrr
    @54
    @59
    @13
    vz
    crp
    @47
    @51
    @30
    @59
    @13
    wi
    @47
    @51
    wa
    #
    @30
    @59
    @13
    @30
    @59
    wa
    @29
    @58
    wa
    #
    vw
    cS
    wral
    @62
    @13
    @29
    @58
    vw
    cS
    r19.26
    @62
    @63
    @12
    vw
    cS
    @62
    @44
    wa
    #
    @29
    @58
    @12
    @64
    @29
    wa
    @57
    @11
    @5
    @64
    @29
    @57
    @11
    wi
    #
    @47
    @44
    @51
    @29
    @65
    wi
    @47
    @44
    wa
    #
    @51
    @29
    @65
    @66
    @51
    @29
    wa
    #
    @50
    @26
    caddc
    co
    #
    @28
    @28
    caddc
    co
    #
    clt
    wbr
    #
    @65
    @66
    @50
    cr
    wcel
    @26
    cr
    wcel
    @28
    cr
    wcel
    #
    @71
    @67
    @70
    wi
    @66
    @49
    @66
    @48
    @7
    @66
    cS
    cc
    @4
    @23
    @66
    @23
    @33
    wcel
    cS
    cc
    @23
    wf
    #
    @66
    cZ
    @33
    @22
    cF
    @21
    @34
    @43
    @44
    @42
    ad2antrr
    @21
    @43
    @44
    simplr
    ffvelrnd
    @23
    cc
    cS
    elmapi
    syl
    #
    @47
    @18
    @44
    @52
    adantr
    #
    ffvelrnd
    #
    @66
    cS
    cc
    @4
    cG
    wph
    @2
    @20
    @43
    @44
    @17
    ad3antrrr
    #
    @74
    ffvelrnd
    #
    subcld
    abscld
    #
    @66
    @25
    @66
    @24
    @6
    @47
    @44
    @72
    @24
    cc
    wcel
    @73
    cS
    cc
    @3
    @23
    ffvelrn
    sylancom
    #
    @47
    @44
    @2
    @6
    cc
    wcel
    @76
    cS
    cc
    @3
    cG
    ffvelrn
    sylancom
    #
    subcld
    abscld
    #
    @66
    @28
    @66
    @27
    @47
    @45
    @44
    @61
    adantr
    #
    rphalfcld
    rpred
    #
    @83
    @50
    @26
    @28
    @28
    lt2add
    syl22anc
    @66
    @70
    @68
    @27
    clt
    wbr
    #
    @65
    @66
    @69
    @27
    @68
    clt
    @66
    @27
    @66
    @27
    @66
    @27
    @82
    rpred
    #
    recnd
    2halvesd
    breq2d
    @66
    @84
    @57
    @11
    @66
    @84
    @57
    wa
    #
    @68
    @56
    caddc
    co
    #
    @27
    @27
    caddc
    co
    #
    clt
    wbr
    #
    @11
    @66
    @68
    cr
    wcel
    @56
    cr
    wcel
    @27
    cr
    wcel
    #
    @90
    @86
    @89
    wi
    @66
    @50
    @26
    @78
    @81
    readdcld
    #
    @66
    @55
    @66
    @24
    @48
    @79
    @75
    subcld
    abscld
    #
    @85
    @85
    @68
    @56
    @27
    @27
    lt2add
    syl22anc
    @66
    @89
    @87
    @10
    clt
    wbr
    #
    @11
    @66
    @88
    @10
    @87
    clt
    @66
    @10
    @66
    @10
    @21
    @10
    cr
    wcel
    #
    @43
    @44
    @19
    @94
    wph
    @18
    @10
    rpre
    ad2antll
    ad2antrr
    #
    recnd
    2halvesd
    breq2d
    @66
    @9
    @87
    cle
    wbr
    #
    @93
    @11
    @66
    @9
    @50
    @6
    @48
    cmin
    co
    #
    cabs
    cfv
    #
    caddc
    co
    #
    @87
    @66
    @8
    @66
    @6
    @7
    @80
    @77
    subcld
    abscld
    #
    @66
    @50
    @98
    @78
    @66
    @97
    @66
    @6
    @48
    @80
    @75
    subcld
    abscld
    #
    readdcld
    @66
    @68
    @56
    @91
    @92
    readdcld
    #
    @66
    @9
    @98
    @50
    caddc
    co
    @99
    cle
    @66
    @6
    @7
    @48
    @80
    @77
    @75
    abs3difd
    @66
    @98
    @50
    @66
    @98
    @101
    recnd
    @66
    @50
    @78
    recnd
    #
    addcomd
    breqtrd
    @66
    @99
    @50
    @26
    @56
    caddc
    co
    #
    caddc
    co
    @87
    cle
    @66
    @98
    @104
    @50
    @101
    @66
    @26
    @56
    @81
    @92
    readdcld
    @78
    @66
    @98
    @6
    @24
    cmin
    co
    cabs
    cfv
    #
    @56
    caddc
    co
    @104
    cle
    @66
    @6
    @48
    @24
    @80
    @75
    @79
    abs3difd
    @66
    @105
    @26
    @56
    caddc
    @66
    @6
    @24
    @80
    @79
    abssubd
    oveq1d
    breqtrd
    leadd2dd
    @66
    @50
    @26
    @56
    @103
    @66
    @26
    @81
    recnd
    @66
    @56
    @92
    recnd
    addassd
    breqtrrd
    letrd
    @66
    @9
    cr
    wcel
    @87
    cr
    wcel
    @94
    @96
    @93
    wa
    @11
    wi
    @100
    @102
    @95
    @9
    @87
    @10
    lelttr
    syl3anc
    mpand
    sylbid
    syld
    expd
    sylbid
    syld
    expdimp
    an32s
    imp
    imim2d
    expimpd
    ralimdva
    syl5bir
    expdimp
    an32s
    reximdv
    mpd
    exp31
    mpdd
    rexlimdva
    syl5
    mpd
    ralrimivva
    wph
    @41
    cc
    cc
    wss
    @1
    @2
    @15
    wa
    wb
    wph
    cM
    cF
    cfv
    #
    @0
    wcel
    @41
    wph
    cZ
    @0
    cM
    cF
    ulmcn.f
    wph
    cM
    cM
    cuz
    cfv
    #
    cZ
    wph
    @32
    cM
    @107
    wcel
    ulmcn.m
    cM
    uzid
    syl
    ulmcn.z
    syl6eleqr
    ffvelrnd
    cS
    cc
    @106
    cncfrss
    syl
    cc
    ssid
    vx
    vy
    vz
    vw
    cS
    cc
    cG
    elcncf2
    sylancl
    mpbir2and
end
