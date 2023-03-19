include "cz.mm"
include "wcel.mm"
include "cr.mm"
include "wf.mm"
include "clsp.mm"
include "cfv.mm"
include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "csup.mm"
include "cvv.mm"
include "wa.mm"
include "xrltso.mm"
include "supex.mm"
include "a1i.mm"
include "cmpt.mm"
include "wceq.mm"
include "limsupgval.mm"
include "adantl.mm"
include "wrex.mm"
include "simpl3.mm"
include "wss.mm"
include "wb.mm"
include "cuz.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "zssre.mm"
include "sstri.mm"
include "simpl2.mm"
include "ressxr.mm"
include "fss.mm"
include "sylancl.mm"
include "pnfxr.mm"
include "limsuplt.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "cle.mm"
include "cfl.mm"
include "cfz.mm"
include "wral.mm"
include "cfn.mm"
include "fzfi.mm"
include "adantr.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "ralrimiva.mm"
include "fimaxre3.mm"
include "sylancr.mm"
include "cif.mm"
include "simpr.mm"
include "ad2antrr.mm"
include "limsupgf.mm"
include "ffvelrni.mm"
include "syl.mm"
include "simprl.mm"
include "sseldi.mm"
include "ifcld.mm"
include "wi.mm"
include "sselda.mm"
include "xrleid.mm"
include "limsupgle.mm"
include "syl211anc.mm"
include "r19.21bi.mm"
include "imp.mm"
include "xrmax1.mm"
include "syl2anc.mm"
include "ffvelrnda.mm"
include "xrletr.mm"
include "mpan2d.mm"
include "mpd.mm"
include "syl6eleq.mm"
include "flcld.mm"
include "elfz5.mm"
include "flge.mm"
include "bitr4d.mm"
include "biimpar.mm"
include "simprr.mm"
include "fveq2.mm"
include "breq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "xrmax2.mm"
include "lecasei.mm"
include "a1d.mm"
include "mpbird.mm"
include "ltpnfd.mm"
include "simplrr.mm"
include "breq1.mm"
include "ifboth.mm"
include "xrlelttrd.mm"
include "rexlimddv.mm"
include "eqbrtrrd.mm"
include "c0.mm"
include "wne.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "syl6ss.mm"
include "df-ss.mm"
include "sylib.mm"
include "eqsstrd.mm"
include "cdm.mm"
include "c1.mm"
include "caddc.mm"
include "simpl1.mm"
include "flcl.mm"
include "peano2zd.mm"
include "zred.mm"
include "max1.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fdm.mm"
include "eleqtrrd.mm"
include "fllep1.mm"
include "max2.mm"
include "letrd.mm"
include "elicopnf.mm"
include "mpbir2and.mm"
include "inelcm.mm"
include "imadisj.mm"
include "necon3bii.mm"
include "sylibr.mm"
include "eqnetrd.mm"
include "supxrre1.mm"
include "eqeltrd.mm"
include "fmpt2d.mm"

theorem limsupgre
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  let cA: class A
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vf: setvar f
  let vj: setvar j
  let cC: class C
  let va: setvar a
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  assume limsupval.1: |- G = ( k e. RR |-> sup ( ( ( F " ( k [,) +oo ) ) i^i RR* ) , RR* , < ) )
  assume limsupgre.z: |- Z = ( ZZ>= ` M )

  disjoint F k
  disjoint M k
  disjoint Z k
  disjoint k x
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint F x
  disjoint f k
  disjoint G x
  disjoint A j
  disjoint B j
  disjoint C j
  disjoint C k
  disjoint C x
  disjoint j k
  disjoint j x
  disjoint F j
  disjoint G j
  disjoint F a
  disjoint F i
  disjoint F m
  disjoint F n
  disjoint F r
  disjoint a i
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint m n
  disjoint m r
  disjoint n r
  disjoint G a
  disjoint G i
  disjoint G m
  disjoint G n
  disjoint G r
  disjoint M a
  disjoint M i
  disjoint M m
  disjoint M n
  disjoint M r
  disjoint Z a
  disjoint Z i
  disjoint Z m
  disjoint Z n
  disjoint Z r
  disjoint a k
  disjoint i k
  disjoint k m
  disjoint k n
  disjoint k r
  assert |- ( ( M e. ZZ /\ F : Z --> RR /\ ( limsup ` F ) < +oo ) -> G : RR --> RR )

  proof
    cM
    cz
    wcel
    #
    cZ
    cr
    cF
    wf
    #
    cF
    clsp
    cfv
    cpnf
    clt
    wbr
    #
    w3a
    #
    vk
    va
    cr
    cF
    vk
    cv
    #
    cpnf
    cico
    co
    cima
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cr
    cG
    cvv
    @6
    cvv
    wcel
    @3
    @4
    cr
    wcel
    wa
    cxr
    @5
    clt
    xrltso
    supex
    a1i
    cG
    vk
    cr
    @6
    cmpt
    wceq
    @3
    limsupval.1
    a1i
    @3
    va
    cv
    #
    cr
    wcel
    #
    wa
    #
    @7
    cG
    cfv
    #
    cF
    @7
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cr
    @8
    @10
    @14
    wceq
    @3
    vk
    cF
    cG
    @7
    limsupval.1
    limsupgval
    adantl
    #
    @9
    @14
    cr
    wcel
    #
    @14
    cpnf
    clt
    wbr
    #
    @9
    @10
    @14
    cpnf
    clt
    @15
    @9
    vn
    cv
    #
    cG
    cfv
    #
    cpnf
    clt
    wbr
    #
    @10
    cpnf
    clt
    wbr
    #
    vn
    cr
    @9
    @2
    @20
    vn
    cr
    wrex
    #
    @0
    @1
    @2
    @8
    simpl3
    @9
    cZ
    cr
    wss
    #
    cZ
    cxr
    cF
    wf
    #
    cpnf
    cxr
    wcel
    #
    @2
    @22
    wb
    @23
    @9
    cZ
    cz
    cr
    cZ
    cM
    cuz
    cfv
    #
    cz
    limsupgre.z
    cM
    uzssz
    eqsstri
    #
    zssre
    sstri
    #
    a1i
    @9
    @1
    cr
    cxr
    wss
    @24
    @0
    @1
    @2
    @8
    simpl2
    #
    ressxr
    cZ
    cr
    cxr
    cF
    fss
    sylancl
    #
    @25
    @9
    pnfxr
    a1i
    cpnf
    cZ
    vn
    vk
    cF
    cG
    limsupval.1
    limsuplt
    syl3anc
    mpbid
    @9
    @18
    cr
    wcel
    #
    @20
    wa
    #
    wa
    #
    vm
    cv
    #
    cF
    cfv
    #
    vr
    cv
    #
    cle
    wbr
    #
    vm
    cM
    @18
    cfl
    cfv
    #
    cfz
    co
    #
    wral
    #
    @21
    vr
    cr
    @33
    @39
    cfn
    wcel
    @35
    cr
    wcel
    #
    vm
    @39
    wral
    @40
    vr
    cr
    wrex
    cM
    @38
    fzfi
    @33
    @41
    vm
    @39
    @33
    @1
    @34
    cZ
    wcel
    @41
    @34
    @39
    wcel
    #
    @9
    @1
    @32
    @29
    adantr
    @42
    @34
    @26
    cZ
    @34
    cM
    @38
    elfzuz
    limsupgre.z
    syl6eleqr
    cZ
    cr
    @34
    cF
    ffvelrn
    syl2an
    ralrimiva
    vr
    vm
    @39
    @35
    fimaxre3
    sylancr
    @33
    @36
    cr
    wcel
    #
    @40
    wa
    #
    wa
    #
    @10
    @19
    @36
    cle
    wbr
    #
    @36
    @19
    cif
    #
    cpnf
    @45
    @8
    @10
    cxr
    wcel
    @9
    @8
    @32
    @44
    @3
    @8
    simpr
    #
    ad2antrr
    #
    cr
    cxr
    @7
    cG
    vk
    cF
    cG
    limsupval.1
    limsupgf
    #
    ffvelrni
    syl
    @45
    @46
    @36
    @19
    cxr
    @45
    cr
    cxr
    @36
    ressxr
    @33
    @43
    @40
    simprl
    #
    sseldi
    #
    @45
    @31
    @19
    cxr
    wcel
    #
    @33
    @31
    @44
    @9
    @31
    @20
    simprl
    #
    adantr
    #
    cr
    cxr
    @18
    cG
    @50
    ffvelrni
    #
    syl
    #
    ifcld
    #
    @25
    @45
    pnfxr
    a1i
    @45
    @10
    @47
    cle
    wbr
    #
    @7
    vi
    cv
    #
    cle
    wbr
    #
    @60
    cF
    cfv
    #
    @47
    cle
    wbr
    #
    wi
    #
    vi
    cZ
    wral
    #
    @45
    @64
    vi
    cZ
    @45
    @60
    cZ
    wcel
    #
    wa
    #
    @63
    @61
    @67
    @63
    @18
    @60
    @33
    @31
    @44
    @66
    @54
    ad2antrr
    #
    @45
    cZ
    cr
    @60
    @23
    @45
    @28
    a1i
    #
    sselda
    @67
    @18
    @60
    cle
    wbr
    #
    wa
    @62
    @19
    cle
    wbr
    #
    @63
    @67
    @70
    @71
    @45
    @70
    @71
    wi
    #
    vi
    cZ
    @45
    @19
    @19
    cle
    wbr
    #
    @72
    vi
    cZ
    wral
    #
    @45
    @53
    @73
    @57
    @19
    xrleid
    syl
    @45
    @23
    @24
    @31
    @53
    @73
    @74
    wb
    @69
    @9
    @24
    @32
    @44
    @30
    ad2antrr
    #
    @55
    @57
    @19
    cZ
    @18
    vi
    vk
    cF
    cG
    limsupval.1
    limsupgle
    syl211anc
    mpbid
    r19.21bi
    imp
    @67
    @71
    @63
    wi
    @70
    @67
    @71
    @19
    @47
    cle
    wbr
    #
    @63
    @67
    @53
    @36
    cxr
    wcel
    #
    @76
    @67
    @31
    @53
    @68
    @56
    syl
    #
    @45
    @77
    @66
    @52
    adantr
    #
    @19
    @36
    xrmax1
    syl2anc
    @67
    @62
    cxr
    wcel
    #
    @53
    @47
    cxr
    wcel
    #
    @71
    @76
    wa
    @63
    wi
    @45
    cZ
    cxr
    @60
    cF
    @75
    ffvelrnda
    #
    @78
    @45
    @81
    @66
    @58
    adantr
    #
    @62
    @19
    @47
    xrletr
    syl3anc
    mpan2d
    adantr
    mpd
    @67
    @60
    @18
    cle
    wbr
    #
    wa
    #
    @62
    @36
    cle
    wbr
    #
    @63
    @85
    @60
    @39
    wcel
    #
    @40
    @86
    @67
    @87
    @84
    @67
    @87
    @60
    @38
    cle
    wbr
    #
    @84
    @67
    @60
    @26
    wcel
    @38
    cz
    wcel
    #
    @87
    @88
    wb
    @67
    @60
    cZ
    @26
    @45
    @66
    simpr
    #
    limsupgre.z
    syl6eleq
    @45
    @89
    @66
    @45
    @18
    @55
    flcld
    adantr
    @60
    cM
    @38
    elfz5
    syl2anc
    @67
    @31
    @60
    cz
    wcel
    @84
    @88
    wb
    @68
    @67
    cZ
    cz
    @60
    @27
    @90
    sseldi
    @18
    @60
    flge
    syl2anc
    bitr4d
    biimpar
    @45
    @40
    @66
    @84
    @33
    @43
    @40
    simprr
    ad2antrr
    @37
    @86
    vm
    @60
    @39
    @34
    @60
    wceq
    @35
    @62
    @36
    cle
    @34
    @60
    cF
    fveq2
    breq1d
    rspcv
    sylc
    @67
    @86
    @63
    wi
    @84
    @67
    @86
    @36
    @47
    cle
    wbr
    #
    @63
    @45
    @91
    @66
    @45
    @53
    @77
    @91
    @57
    @52
    @19
    @36
    xrmax2
    syl2anc
    adantr
    @67
    @80
    @77
    @81
    @86
    @91
    wa
    @63
    wi
    @82
    @79
    @83
    @62
    @36
    @47
    xrletr
    syl3anc
    mpan2d
    adantr
    mpd
    lecasei
    a1d
    ralrimiva
    @45
    @23
    @24
    @8
    @81
    @59
    @65
    wb
    @69
    @75
    @49
    @58
    @47
    cZ
    @7
    vi
    vk
    cF
    cG
    limsupval.1
    limsupgle
    syl211anc
    mpbird
    @45
    @36
    cpnf
    clt
    wbr
    #
    @20
    @47
    cpnf
    clt
    wbr
    #
    @45
    @36
    @51
    ltpnfd
    @9
    @31
    @20
    @44
    simplrr
    @46
    @92
    @20
    @93
    @36
    @19
    @36
    @47
    cpnf
    clt
    breq1
    @19
    @47
    cpnf
    clt
    breq1
    ifboth
    syl2anc
    xrlelttrd
    rexlimddv
    rexlimddv
    eqbrtrrd
    @9
    @13
    cr
    wss
    @13
    c0
    wne
    @16
    @17
    wb
    @9
    @13
    @12
    cr
    @9
    @12
    cxr
    wss
    @13
    @12
    wceq
    @9
    @12
    cr
    cxr
    @9
    @12
    cF
    crn
    #
    cr
    cF
    @11
    imassrn
    @9
    @1
    @94
    cr
    wss
    @29
    cZ
    cr
    cF
    frn
    syl
    syl5ss
    #
    ressxr
    syl6ss
    @12
    cxr
    df-ss
    sylib
    #
    @95
    eqsstrd
    @9
    @13
    @12
    c0
    @96
    @9
    cF
    cdm
    #
    @11
    cin
    #
    c0
    wne
    #
    @12
    c0
    wne
    @9
    cM
    @7
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @101
    cM
    cif
    #
    @97
    wcel
    @103
    @11
    wcel
    #
    @99
    @9
    @103
    cZ
    @97
    @9
    @103
    @26
    cZ
    @9
    @0
    @103
    cz
    wcel
    cM
    @103
    cle
    wbr
    #
    @103
    @26
    wcel
    @0
    @1
    @2
    @8
    simpl1
    #
    @9
    @102
    @101
    cM
    cz
    @9
    @100
    @8
    @100
    cz
    wcel
    @3
    @7
    flcl
    adantl
    peano2zd
    #
    @106
    ifcld
    #
    @9
    cM
    cr
    wcel
    #
    @101
    cr
    wcel
    #
    @105
    @9
    cM
    @106
    zred
    #
    @9
    @101
    @107
    zred
    #
    cM
    @101
    max1
    syl2anc
    cM
    @103
    eluz2
    syl3anbrc
    limsupgre.z
    syl6eleqr
    @9
    @1
    @97
    cZ
    wceq
    @29
    cZ
    cr
    cF
    fdm
    syl
    eleqtrrd
    @9
    @104
    @103
    cr
    wcel
    #
    @7
    @103
    cle
    wbr
    #
    @9
    @103
    @108
    zred
    #
    @9
    @7
    @101
    @103
    @48
    @112
    @115
    @8
    @7
    @101
    cle
    wbr
    @3
    @7
    fllep1
    adantl
    @9
    @109
    @110
    @101
    @103
    cle
    wbr
    @111
    @112
    cM
    @101
    max2
    syl2anc
    letrd
    @8
    @104
    @113
    @114
    wa
    wb
    @3
    @7
    @103
    elicopnf
    adantl
    mpbir2and
    @103
    @97
    @11
    inelcm
    syl2anc
    @12
    c0
    @98
    c0
    cF
    @11
    imadisj
    necon3bii
    sylibr
    eqnetrd
    @13
    supxrre1
    syl2anc
    mpbird
    eqeltrd
    fmpt2d
end
