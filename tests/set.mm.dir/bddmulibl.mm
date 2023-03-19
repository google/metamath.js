include "cmbf.mm"
include "wcel.mm"
include "cibl.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cdm.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "wa.mm"
include "cin.mm"
include "cmpt.mm"
include "cvol.mm"
include "cc.mm"
include "wf.mm"
include "wfn.mm"
include "mbff.mm"
include "ad2antrr.mm"
include "ffn.mm"
include "syl.mm"
include "iblmbf.mm"
include "ad2antlr.mm"
include "mbfdm.mm"
include "eqid.mm"
include "eqidd.mm"
include "offval.mm"
include "cvv.mm"
include "ovexd.mm"
include "simpll.mm"
include "mbfmul.mm"
include "eqeltrrd.mm"
include "cc0.mm"
include "cif.mm"
include "citg2.mm"
include "ccom.mm"
include "mbfmptcl.mm"
include "absf.mm"
include "a1i.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "ccncf.mm"
include "fmptd.mm"
include "wss.mm"
include "ax-resscn.mm"
include "ssid.mm"
include "cncfss.mm"
include "mp2an.mm"
include "abscncf.mm"
include "sselii.mm"
include "cncombf.mm"
include "syl3anc.mm"
include "cpnf.mm"
include "cicc.mm"
include "cxr.mm"
include "abscld.mm"
include "rexrd.mm"
include "absge0d.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "wn.mm"
include "0e0iccpnf.mm"
include "ifclda.mm"
include "adantr.mm"
include "c0.mm"
include "wceq.mm"
include "csn.mm"
include "cxp.mm"
include "cico.mm"
include "reex.mm"
include "simprl.mm"
include "elin.mm"
include "simprbi.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "elrege0.mm"
include "0e0icopnf.mm"
include "fconstmpt.mm"
include "offval2.mm"
include "ovif2.mm"
include "recnd.mm"
include "mul01d.mm"
include "ifeq2d.mm"
include "syl5eq.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "inss2.mm"
include "mbfdm2.mm"
include "ffvelrnda.mm"
include "simplr.mm"
include "iblss.mm"
include "iblabs.mm"
include "iblpos.mm"
include "mpbid.mm"
include "simprd.mm"
include "simplrl.mm"
include "wex.mm"
include "neq0.mm"
include "0re.mm"
include "simplbi.mm"
include "simprr.mm"
include "breq1d.mm"
include "rspccva.mm"
include "letrd.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "imp.mm"
include "itg2mulc.mm"
include "eqtr3d.mm"
include "remulcld.mm"
include "eqeltrd.mm"
include "noel.mm"
include "eleq2.mm"
include "mtbiri.mm"
include "iffalse.mm"
include "syl6eqr.mm"
include "itg20.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "pm2.61d2.mm"
include "cofr.mm"
include "mulge0d.mm"
include "absmuld.mm"
include "abscl.mm"
include "absge0.mm"
include "jca.mm"
include "lemul1a.mm"
include "syl31anc.mm"
include "eqbrtrd.mm"
include "iftrue.mm"
include "adantl.mm"
include "3brtr4d.mm"
include "0le0.mm"
include "pm2.61dan.mm"
include "ralrimivw.mm"
include "ofrfval2.mm"
include "mpbird.mm"
include "itg2le.mm"
include "itg2lecl.mm"
include "mpbir2and.mm"
include "iblabsr.mm"
include "rexlimdvaa.mm"
include "3impia.mm"

theorem bddmulibl
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cA: class A
  let cB: class B
  let vz: setvar z

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint G z
  assert |- ( ( F e. MblFn /\ G e. L^1 /\ E. x e. RR A. y e. dom F ( abs ` ( F ` y ) ) <_ x ) -> ( F oF x. G ) e. L^1 )

  proof
    cF
    cmbf
    wcel
    #
    cG
    cibl
    wcel
    #
    vy
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vy
    cF
    cdm
    #
    wral
    #
    vx
    cr
    wrex
    cF
    cG
    cmul
    cof
    #
    co
    #
    cibl
    wcel
    #
    @0
    @1
    wa
    #
    @8
    @11
    vx
    cr
    @12
    @5
    cr
    wcel
    #
    @8
    wa
    #
    wa
    #
    @10
    vz
    @7
    cG
    cdm
    #
    cin
    #
    vz
    cv
    #
    cF
    cfv
    #
    @18
    cG
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cibl
    @15
    vz
    @7
    @16
    @19
    @20
    cmul
    @17
    cF
    cG
    cvol
    cdm
    #
    @23
    @15
    @7
    cc
    cF
    wf
    #
    cF
    @7
    wfn
    @0
    @24
    @1
    @14
    cF
    mbff
    ad2antrr
    #
    @7
    cc
    cF
    ffn
    syl
    @15
    @16
    cc
    cG
    wf
    #
    cG
    @16
    wfn
    @15
    cG
    cmbf
    wcel
    #
    @26
    @1
    @27
    @0
    @14
    cG
    iblmbf
    ad2antlr
    #
    cG
    mbff
    syl
    #
    @16
    cc
    cG
    ffn
    syl
    @0
    @7
    @23
    wcel
    @1
    @14
    cF
    mbfdm
    ad2antrr
    @15
    @27
    @16
    @23
    wcel
    @28
    cG
    mbfdm
    syl
    @17
    eqid
    @15
    @18
    @7
    wcel
    #
    wa
    @19
    eqidd
    @15
    @18
    @16
    wcel
    #
    wa
    @20
    eqidd
    offval
    #
    @15
    vz
    @17
    @21
    cvv
    @15
    @18
    @17
    wcel
    #
    wa
    #
    @19
    @20
    cmul
    ovexd
    #
    @15
    @10
    @22
    cmbf
    @32
    @15
    cF
    cG
    @0
    @1
    @14
    simpll
    @28
    mbfmul
    eqeltrrd
    #
    @15
    vz
    @17
    @21
    cabs
    cfv
    #
    cmpt
    #
    cibl
    wcel
    @38
    cmbf
    wcel
    vz
    cr
    @33
    @37
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    #
    @15
    cabs
    @22
    ccom
    #
    @38
    cmbf
    @15
    vz
    vy
    @17
    cc
    @21
    @2
    cabs
    cfv
    @37
    @22
    cabs
    @15
    vz
    @17
    @21
    cvv
    @36
    @35
    mbfmptcl
    #
    @15
    @22
    eqidd
    @15
    vy
    cc
    cr
    cabs
    cc
    cr
    cabs
    wf
    @15
    absf
    a1i
    feqmptd
    @2
    @21
    cabs
    fveq2
    fmptco
    @15
    @22
    cmbf
    wcel
    @17
    cc
    @22
    wf
    cabs
    cc
    cc
    ccncf
    co
    #
    wcel
    #
    @43
    cmbf
    wcel
    @36
    @15
    vz
    @17
    @21
    cc
    @22
    @44
    @22
    eqid
    fmptd
    @46
    @15
    cc
    cr
    ccncf
    co
    #
    @45
    cabs
    cr
    cc
    wss
    cc
    cc
    wss
    @47
    @45
    wss
    ax-resscn
    cc
    ssid
    cc
    cr
    cc
    cncfss
    mp2an
    abscncf
    sselii
    a1i
    @17
    cc
    @22
    cabs
    cncombf
    syl3anc
    eqeltrrd
    @15
    cr
    cc0
    cpnf
    cicc
    co
    #
    @40
    wf
    #
    vz
    cr
    @33
    @5
    @20
    cabs
    cfv
    #
    cmul
    co
    #
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    #
    @41
    @54
    cle
    wbr
    #
    @42
    @15
    vz
    cr
    @39
    @48
    @40
    @15
    @39
    @48
    wcel
    @18
    cr
    wcel
    #
    @15
    @33
    @37
    cc0
    @48
    @34
    @37
    cxr
    wcel
    cc0
    @37
    cle
    wbr
    @37
    @48
    wcel
    @34
    @37
    @34
    @21
    @44
    abscld
    #
    rexrd
    @34
    @21
    @44
    absge0d
    #
    @37
    elxrge0
    sylanbrc
    cc0
    @48
    wcel
    @15
    @33
    wn
    #
    wa
    #
    0e0iccpnf
    a1i
    #
    ifclda
    adantr
    #
    @40
    eqid
    fmptd
    #
    @15
    @17
    c0
    wceq
    #
    @55
    @15
    @65
    wn
    #
    @55
    @15
    @66
    wa
    #
    @54
    @5
    vz
    cr
    @33
    @50
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    cr
    @67
    cr
    @5
    csn
    cxp
    #
    @69
    @9
    co
    #
    citg2
    cfv
    @54
    @71
    @67
    @73
    @53
    citg2
    @67
    @73
    vz
    cr
    @5
    @68
    cmul
    co
    #
    cmpt
    @53
    @67
    vz
    cr
    @5
    @68
    cmul
    @72
    @69
    cvv
    cr
    cc0
    cpnf
    cico
    co
    #
    cr
    cvv
    wcel
    #
    @67
    reex
    a1i
    @15
    @13
    @66
    @57
    @12
    @13
    @8
    simprl
    #
    ad2antrr
    @15
    @68
    @75
    wcel
    #
    @66
    @57
    @15
    @33
    @50
    cc0
    @75
    @34
    @50
    cr
    wcel
    #
    cc0
    @50
    cle
    wbr
    #
    @50
    @75
    wcel
    @34
    @20
    @15
    @26
    @31
    @20
    cc
    wcel
    #
    @33
    @29
    @33
    @30
    @31
    @18
    @7
    @16
    elin
    #
    simprbi
    @16
    cc
    @18
    cG
    ffvelrn
    syl2an
    #
    abscld
    #
    @34
    @20
    @83
    absge0d
    #
    @50
    elrege0
    sylanbrc
    cc0
    @75
    wcel
    @61
    0e0icopnf
    a1i
    ifclda
    #
    ad2antrr
    @72
    vz
    cr
    @5
    cmpt
    wceq
    @67
    vz
    cr
    @5
    fconstmpt
    a1i
    @67
    @69
    eqidd
    offval2
    @67
    vz
    cr
    @74
    @52
    @67
    @74
    @33
    @51
    @5
    cc0
    cmul
    co
    #
    cif
    @52
    @33
    @5
    @50
    cc0
    cmul
    ovif2
    @67
    @33
    @87
    cc0
    @51
    @67
    @5
    @15
    @5
    cc
    wcel
    @66
    @15
    @5
    @77
    recnd
    adantr
    mul01d
    ifeq2d
    syl5eq
    mpteq2dv
    eqtrd
    fveq2d
    @67
    @5
    @69
    @15
    cr
    @75
    @69
    wf
    @66
    @15
    vz
    cr
    @68
    @75
    @69
    @15
    @78
    @57
    @86
    adantr
    @69
    eqid
    fmptd
    adantr
    @15
    @70
    cr
    wcel
    #
    @66
    @15
    vz
    @17
    @50
    cmpt
    #
    cmbf
    wcel
    #
    @88
    @15
    @89
    cibl
    wcel
    @90
    @88
    wa
    @15
    vz
    @17
    @20
    cc
    @83
    @15
    vz
    @17
    @16
    @20
    cc
    @17
    @16
    wss
    @15
    @7
    @16
    inss2
    a1i
    @15
    vz
    @17
    @21
    cvv
    @36
    @35
    mbfdm2
    @15
    @16
    cc
    @18
    cG
    @29
    ffvelrnda
    @15
    cG
    vz
    @16
    @20
    cmpt
    cibl
    @15
    vz
    @16
    cc
    cG
    @29
    feqmptd
    @0
    @1
    @14
    simplr
    eqeltrrd
    iblss
    iblabs
    @15
    vz
    @17
    @50
    @84
    @85
    iblpos
    mpbid
    simprd
    adantr
    #
    @67
    @13
    cc0
    @5
    cle
    wbr
    #
    @5
    @75
    wcel
    @12
    @13
    @8
    @66
    simplrl
    #
    @15
    @66
    @92
    @66
    @33
    vz
    wex
    @15
    @92
    vz
    @17
    neq0
    @15
    @33
    @92
    vz
    @15
    @33
    @92
    @34
    cc0
    @19
    cabs
    cfv
    #
    @5
    cc0
    cr
    wcel
    @34
    0re
    a1i
    @34
    @19
    @15
    @24
    @30
    @19
    cc
    wcel
    @33
    @25
    @33
    @30
    @31
    @82
    simplbi
    #
    @7
    cc
    @18
    cF
    ffvelrn
    syl2an
    #
    abscld
    #
    @12
    @13
    @8
    @33
    simplrl
    #
    @34
    @19
    @96
    absge0d
    @15
    @8
    @30
    @94
    @5
    cle
    wbr
    #
    @33
    @12
    @13
    @8
    simprr
    @95
    @6
    @99
    vy
    @18
    @7
    @2
    @18
    wceq
    #
    @4
    @94
    @5
    cle
    @100
    @3
    @19
    cabs
    @2
    @18
    cF
    fveq2
    fveq2d
    breq1d
    rspccva
    syl2an
    #
    letrd
    #
    ex
    exlimdv
    syl5bi
    imp
    @5
    elrege0
    sylanbrc
    itg2mulc
    eqtr3d
    @67
    @5
    @70
    @93
    @91
    remulcld
    eqeltrd
    ex
    @65
    @54
    cr
    cc0
    csn
    cxp
    #
    citg2
    cfv
    #
    cr
    @65
    @53
    @103
    citg2
    @65
    @53
    vz
    cr
    cc0
    cmpt
    @103
    @65
    vz
    cr
    @52
    cc0
    @65
    @60
    @52
    cc0
    wceq
    @65
    @33
    @18
    c0
    wcel
    @18
    noel
    @17
    c0
    @18
    eleq2
    mtbiri
    @33
    @51
    cc0
    iffalse
    #
    syl
    mpteq2dv
    vz
    cr
    cc0
    fconstmpt
    syl6eqr
    fveq2d
    @104
    cc0
    cr
    itg20
    0re
    eqeltri
    syl6eqel
    pm2.61d2
    @15
    @49
    cr
    @48
    @53
    wf
    @40
    @53
    cle
    cofr
    wbr
    #
    @56
    @64
    @15
    vz
    cr
    @52
    @48
    @53
    @15
    @52
    @48
    wcel
    @57
    @15
    @33
    @51
    cc0
    @48
    @34
    @51
    cxr
    wcel
    cc0
    @51
    cle
    wbr
    @51
    @48
    wcel
    @34
    @51
    @34
    @5
    @50
    @98
    @84
    remulcld
    rexrd
    @34
    @5
    @50
    @98
    @84
    @102
    @85
    mulge0d
    @51
    elxrge0
    sylanbrc
    @62
    ifclda
    adantr
    #
    @53
    eqid
    fmptd
    @15
    @106
    @39
    @52
    cle
    wbr
    #
    vz
    cr
    wral
    @15
    @108
    vz
    cr
    @15
    @33
    @108
    @34
    @37
    @51
    @39
    @52
    cle
    @34
    @37
    @94
    @50
    cmul
    co
    #
    @51
    cle
    @34
    @19
    @20
    @96
    @83
    absmuld
    @34
    @94
    cr
    wcel
    @13
    @79
    @80
    wa
    #
    @99
    @109
    @51
    cle
    wbr
    @97
    @98
    @34
    @81
    @110
    @83
    @81
    @79
    @80
    @20
    abscl
    @20
    absge0
    jca
    syl
    @101
    @94
    @5
    @50
    lemul1a
    syl31anc
    eqbrtrd
    @33
    @39
    @37
    wceq
    @15
    @33
    @37
    cc0
    iftrue
    adantl
    @33
    @52
    @51
    wceq
    @15
    @33
    @51
    cc0
    iftrue
    adantl
    3brtr4d
    @60
    @108
    @15
    @60
    cc0
    cc0
    @39
    @52
    cle
    cc0
    cc0
    cle
    wbr
    @60
    0le0
    a1i
    @33
    @37
    cc0
    iffalse
    @105
    3brtr4d
    adantl
    pm2.61dan
    ralrimivw
    @15
    vz
    cr
    @39
    @52
    cle
    @40
    @53
    cvv
    @48
    @48
    @76
    @15
    reex
    a1i
    @63
    @107
    @15
    @40
    eqidd
    @15
    @53
    eqidd
    ofrfval2
    mpbird
    @40
    @53
    itg2le
    syl3anc
    @54
    @40
    itg2lecl
    syl3anc
    @15
    vz
    @17
    @37
    @58
    @59
    iblpos
    mpbir2and
    iblabsr
    eqeltrd
    rexlimdvaa
    3impia
end
