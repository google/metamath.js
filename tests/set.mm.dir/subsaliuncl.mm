include "cv.mm"
include "cfv.mm"
include "cin.mm"
include "wceq.mm"
include "cn.mm"
include "wral.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "ciun.mm"
include "wcel.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "wfn.mm"
include "wa.mm"
include "wex.mm"
include "cdom.mm"
include "wbr.mm"
include "com.mm"
include "cen.mm"
include "cvv.mm"
include "csalg.mm"
include "eqid.mm"
include "rabexd.mm"
include "ralrimivw.mm"
include "fnmpt.mm"
include "syl.mm"
include "wi.mm"
include "nnex.mm"
include "fnrndomg.mm"
include "ax-mp.mm"
include "nnenom.mm"
include "a1i.mm"
include "domentr.mm"
include "syl2anc.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "vex.mm"
include "elrnmpt.mm"
include "biimpi.mm"
include "adantl.mm"
include "w3a.mm"
include "simp3.mm"
include "crest.mm"
include "ffvelrnda.mm"
include "syl6eleq.mm"
include "elexd.mm"
include "elrest.mm"
include "adantr.mm"
include "mpbid.mm"
include "rabn0.mm"
include "sylibr.mm"
include "3adant3.mm"
include "eqnetrd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "axccdom.mm"
include "simpl.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rabbidv.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "fneq2i.mm"
include "ad2antrl.mm"
include "raleqi.mm"
include "adantrl.mm"
include "ccom.mm"
include "nfv.mm"
include "3ad2ant1.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "cbvrabv.mm"
include "mpteq2i.mm"
include "eqtr2i.mm"
include "coeq2i.mm"
include "biimpri.mm"
include "3ad2ant2.mm"
include "eqcomi.mm"
include "id.mm"
include "eleq12d.mm"
include "cbvralv.mm"
include "bitri.mm"
include "3ad2ant3.mm"
include "subsaliuncllem.mm"
include "syl3anc.mm"
include "ex.mm"
include "exlimdv.mm"
include "nnct.mm"
include "wf.mm"
include "elmapi.mm"
include "saliuncl.mm"
include "elrestd.mm"
include "nfra1.mm"
include "rspa.mm"
include "iuneq2df.mm"
include "iunin1.mm"
include "eqtrd.mm"
include "mpbird.mm"

theorem subsaliuncl
  let wph: wff ph
  let cD: class D
  let cS: class S
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cV: class V
  let ve: setvar e
  let vf: setvar f
  let vz: setvar z
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume subsaliuncl.1: |- ( ph -> S e. SAlg )
  assume subsaliuncl.2: |- ( ph -> D e. V )
  assume subsaliuncl.3: |- T = ( S |`t D )
  assume subsaliuncl.4: |- ( ph -> F : NN --> T )

  disjoint D n
  disjoint F n
  disjoint S n
  disjoint n ph
  disjoint D e
  disjoint D f
  disjoint D z
  disjoint e f
  disjoint e n
  disjoint e z
  disjoint f n
  disjoint f z
  disjoint n z
  disjoint D m
  disjoint e m
  disjoint m n
  disjoint m z
  disjoint D x
  disjoint D y
  disjoint f x
  disjoint f y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F e
  disjoint F f
  disjoint F z
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint S e
  disjoint S f
  disjoint S z
  disjoint S m
  disjoint S x
  disjoint S y
  disjoint T e
  disjoint e ph
  disjoint f ph
  disjoint ph z
  disjoint m x
  disjoint m y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> U_ n e. NN ( F ` n ) e. T )

  proof
    wph
    vn
    cv
    #
    cF
    cfv
    #
    @0
    ve
    cv
    #
    cfv
    #
    cD
    cin
    #
    wceq
    #
    vn
    cn
    wral
    #
    ve
    cS
    cn
    cmap
    co
    #
    wrex
    #
    vn
    cn
    @1
    ciun
    #
    cT
    wcel
    #
    wph
    vf
    cv
    #
    vn
    cn
    @1
    vx
    cv
    #
    cD
    cin
    #
    wceq
    #
    vx
    cS
    crab
    #
    cmpt
    #
    crn
    #
    wfn
    #
    vy
    cv
    #
    @11
    cfv
    #
    @19
    wcel
    #
    vy
    @17
    wral
    #
    wa
    #
    vf
    wex
    @8
    wph
    vy
    vf
    @17
    wph
    @17
    cn
    cdom
    wbr
    #
    cn
    com
    cen
    wbr
    #
    @17
    com
    cdom
    wbr
    wph
    @16
    cn
    wfn
    #
    @24
    wph
    @15
    cvv
    wcel
    #
    vn
    cn
    wral
    @26
    wph
    @27
    vn
    cn
    wph
    @14
    vx
    cS
    @15
    csalg
    @15
    eqid
    subsaliuncl.1
    rabexd
    ralrimivw
    vn
    cn
    @15
    @16
    cvv
    @16
    eqid
    #
    fnmpt
    syl
    cn
    cvv
    wcel
    @26
    @24
    wi
    nnex
    cn
    cvv
    @16
    fnrndomg
    ax-mp
    syl
    @25
    wph
    nnenom
    a1i
    @17
    cn
    com
    domentr
    syl2anc
    wph
    @19
    @17
    wcel
    #
    wa
    @19
    @15
    wceq
    #
    vn
    cn
    wrex
    #
    @19
    c0
    wne
    #
    @29
    @31
    wph
    @29
    @31
    @19
    cvv
    wcel
    @29
    @31
    wb
    vy
    vex
    vn
    cn
    @15
    @19
    @16
    cvv
    @28
    elrnmpt
    ax-mp
    biimpi
    adantl
    wph
    @31
    @32
    wi
    @29
    wph
    @30
    @32
    vn
    cn
    wph
    @0
    cn
    wcel
    #
    @30
    @32
    wph
    @33
    @30
    w3a
    @19
    @15
    c0
    wph
    @33
    @30
    simp3
    wph
    @33
    @15
    c0
    wne
    #
    @30
    wph
    @33
    wa
    #
    @14
    vx
    cS
    wrex
    #
    @34
    @35
    @1
    cS
    cD
    crest
    co
    #
    wcel
    #
    @36
    @35
    @1
    cT
    @37
    wph
    cn
    cT
    @0
    cF
    subsaliuncl.4
    ffvelrnda
    subsaliuncl.3
    syl6eleq
    wph
    @38
    @36
    wb
    #
    @33
    wph
    cS
    csalg
    wcel
    #
    cD
    cvv
    wcel
    #
    @39
    subsaliuncl.1
    wph
    cD
    cV
    subsaliuncl.2
    elexd
    #
    vx
    @1
    cD
    cS
    csalg
    cvv
    elrest
    syl2anc
    adantr
    mpbid
    @14
    vx
    cS
    rabn0
    sylibr
    3adant3
    eqnetrd
    3exp
    rexlimdv
    adantr
    mpd
    axccdom
    wph
    @23
    @8
    vf
    wph
    @23
    @8
    wph
    @23
    wa
    wph
    @11
    vm
    cn
    vm
    cv
    #
    cF
    cfv
    #
    @13
    wceq
    #
    vx
    cS
    crab
    #
    cmpt
    #
    crn
    #
    wfn
    #
    @21
    vy
    @48
    wral
    #
    @8
    wph
    @23
    simpl
    @18
    @49
    wph
    @22
    @18
    @49
    @17
    @48
    @11
    @16
    @47
    vn
    vm
    cn
    @15
    @46
    @0
    @43
    wceq
    #
    @14
    @45
    vx
    cS
    @51
    @1
    @44
    @13
    @0
    @43
    cF
    fveq2
    eqeq1d
    rabbidv
    cbvmptv
    #
    rneqi
    #
    fneq2i
    #
    biimpi
    ad2antrl
    wph
    @22
    @50
    @18
    @22
    @50
    wph
    @22
    @50
    @21
    vy
    @17
    @48
    @53
    raleqi
    biimpi
    adantl
    adantrl
    wph
    @49
    @50
    w3a
    #
    vx
    vz
    cD
    cS
    ve
    vn
    @11
    vm
    cn
    @44
    vz
    cv
    #
    cD
    cin
    #
    wceq
    #
    vz
    cS
    crab
    #
    cmpt
    #
    ccom
    cF
    @16
    @11
    csalg
    @55
    vz
    nfv
    wph
    @49
    @40
    @50
    subsaliuncl.1
    3ad2ant1
    @28
    @60
    @16
    @11
    @16
    @47
    @60
    @52
    vm
    cn
    @46
    @59
    @45
    @58
    vx
    vz
    cS
    @12
    @56
    wceq
    @13
    @57
    @44
    @12
    @56
    cD
    ineq1
    eqeq2d
    cbvrabv
    mpteq2i
    eqtr2i
    coeq2i
    @49
    wph
    @18
    @50
    @18
    @49
    @54
    biimpri
    3ad2ant2
    @50
    wph
    @56
    @11
    cfv
    #
    @56
    wcel
    #
    vz
    @17
    wral
    #
    @49
    @50
    @63
    @50
    @22
    @63
    @21
    vy
    @48
    @17
    @17
    @48
    @53
    eqcomi
    raleqi
    @21
    @62
    vy
    vz
    @17
    @19
    @56
    wceq
    #
    @20
    @61
    @19
    @56
    @19
    @56
    @11
    fveq2
    @64
    id
    eleq12d
    cbvralv
    bitri
    biimpi
    3ad2ant3
    subsaliuncllem
    syl3anc
    ex
    exlimdv
    mpd
    wph
    @6
    @10
    ve
    @7
    wph
    @2
    @7
    wcel
    #
    @6
    @10
    wph
    @65
    @6
    w3a
    #
    @10
    vn
    cn
    @3
    ciun
    #
    cD
    cin
    #
    @37
    wcel
    @66
    @68
    cD
    cS
    csalg
    cvv
    @67
    wph
    @65
    @40
    @6
    subsaliuncl.1
    3ad2ant1
    wph
    @65
    @41
    @6
    @42
    3ad2ant1
    wph
    @65
    @67
    cS
    wcel
    @6
    wph
    @65
    wa
    #
    cS
    vn
    @3
    cn
    wph
    @40
    @65
    subsaliuncl.1
    adantr
    cn
    com
    cdom
    wbr
    @69
    nnct
    a1i
    @69
    cn
    cS
    @0
    @2
    @65
    cn
    cS
    @2
    wf
    wph
    @2
    cS
    cn
    elmapi
    adantl
    ffvelrnda
    saliuncl
    3adant3
    @68
    eqid
    elrestd
    @66
    @9
    @68
    cT
    @37
    @6
    wph
    @9
    @68
    wceq
    @65
    @6
    @9
    vn
    cn
    @4
    ciun
    #
    @68
    @6
    vn
    cn
    @1
    @4
    @5
    vn
    cn
    nfra1
    @5
    vn
    cn
    rspa
    iuneq2df
    @70
    @68
    wceq
    @6
    vn
    cn
    cD
    @3
    iunin1
    a1i
    eqtrd
    3ad2ant3
    cT
    @37
    wceq
    @66
    subsaliuncl.3
    a1i
    eleq12d
    mpbird
    3exp
    rexlimdv
    mpd
end
