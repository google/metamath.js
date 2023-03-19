include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "ce.mm"
include "cfv.mm"
include "cabs.mm"
include "cr.mm"
include "cres.mm"
include "ccnv.mm"
include "ci.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "wss.mm"
include "cmpt.mm"
include "wceq.mm"
include "cim.mm"
include "cima.mm"
include "cdm.mm"
include "cnvimass.mm"
include "imf.mm"
include "fdmi.mm"
include "eqcomi.mm"
include "3sstr4i.mm"
include "wf.mm"
include "eff2.mm"
include "a1i.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "resmpt.mm"
include "eqtrd.mm"
include "ax-mp.mm"
include "wcel.mm"
include "sseli.mm"
include "ffvelrni.mm"
include "syl.mm"
include "adantl.mm"
include "wa.mm"
include "crp.mm"
include "wne.mm"
include "simpr.mm"
include "eldifsn.mm"
include "sylib.mm"
include "simpld.mm"
include "simprd.mm"
include "absrpcld.mm"
include "wf1o.mm"
include "reeff1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "mp2b.mm"
include "recnd.mm"
include "ax-icn.mm"
include "adantr.mm"
include "c1.mm"
include "csin.mm"
include "cpi.mm"
include "c2.mm"
include "cneg.mm"
include "cicc.mm"
include "eqid.mm"
include "efif1olem4.mm"
include "3syl.mm"
include "abscld.mm"
include "absne0d.mm"
include "divcld.mm"
include "absdivd.mm"
include "absidm.mm"
include "oveq2d.mm"
include "dividd.mm"
include "3eqtrd.mm"
include "wfn.mm"
include "wb.mm"
include "absf.mm"
include "ffn.mm"
include "fniniseg.mm"
include "sylanbrc.mm"
include "ffvelrnd.mm"
include "sseldd.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addcld.mm"
include "crimd.mm"
include "eqeltrd.mm"
include "elpreima.mm"
include "syl6eleqr.mm"
include "efadd.mm"
include "syl2anc.mm"
include "fvres.mm"
include "f1ocnvfv2.mm"
include "eqtr3d.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "fvex.mm"
include "fvmpt.mm"
include "oveq12d.mm"
include "divcan2d.mm"
include "3eqtrrd.mm"
include "adantrl.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "wi.mm"
include "cre.mm"
include "replimd.mm"
include "absef.mm"
include "recld.mm"
include "eqtr4d.mm"
include "f1ocnvfv1.mm"
include "imcld.mm"
include "efcl.mm"
include "efne0.mm"
include "divcan3d.mm"
include "simprbi.mm"
include "eleq2s.mm"
include "3eqtr4d.mm"
include "syl2an.mm"
include "id.mm"
include "adantrr.mm"
include "impbid.mm"
include "f1o2d.mm"

theorem eff1olem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cD: class D
  let cS: class S
  let cF: class F
  assume eff1olem.1: |- F = ( w e. D |-> ( exp ` ( _i x. w ) ) )
  assume eff1olem.2: |- S = ( `' Im " D )
  assume eff1olem.3: |- ( ph -> D C_ RR )
  assume eff1olem.4: |- ( ( ph /\ ( x e. D /\ y e. D ) ) -> ( abs ` ( x - y ) ) < ( 2 x. _pi ) )
  assume eff1olem.5: |- ( ( ph /\ z e. RR ) -> E. y e. D ( ( z - y ) / ( 2 x. _pi ) ) e. ZZ )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint x y
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S x
  disjoint S y
  assert |- ( ph -> ( exp |` S ) : S -1-1-onto-> ( CC \ { 0 } ) )

  proof
    wph
    vy
    vx
    cS
    cc
    cc0
    csn
    cdif
    #
    vy
    cv
    #
    ce
    cfv
    #
    vx
    cv
    #
    cabs
    cfv
    #
    ce
    cr
    cres
    #
    ccnv
    #
    cfv
    #
    ci
    @3
    @4
    cdiv
    co
    #
    cF
    ccnv
    #
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    ce
    cS
    cres
    #
    cS
    cc
    wss
    #
    @13
    vy
    cS
    @2
    cmpt
    #
    wceq
    cim
    ccnv
    cD
    cima
    #
    cim
    cdm
    #
    cS
    cc
    cim
    cD
    cnvimass
    eff1olem.2
    @17
    cc
    cc
    cr
    cim
    imf
    fdmi
    eqcomi
    3sstr4i
    #
    @14
    @13
    vy
    cc
    @2
    cmpt
    #
    cS
    cres
    @15
    @14
    ce
    @19
    cS
    @14
    vy
    cc
    @0
    ce
    cc
    @0
    ce
    wf
    @14
    eff2
    a1i
    feqmptd
    reseq1d
    vy
    cc
    cS
    @2
    resmpt
    eqtrd
    ax-mp
    @1
    cS
    wcel
    #
    @2
    @0
    wcel
    #
    wph
    @20
    @1
    cc
    wcel
    #
    @21
    cS
    cc
    @1
    @18
    sseli
    #
    cc
    @0
    @1
    ce
    eff2
    ffvelrni
    syl
    adantl
    wph
    @3
    @0
    wcel
    #
    wa
    #
    @12
    @16
    cS
    @25
    @12
    cc
    wcel
    #
    @12
    cim
    cfv
    #
    cD
    wcel
    #
    @12
    @16
    wcel
    #
    @25
    @7
    @11
    @25
    @7
    @25
    @4
    crp
    wcel
    #
    @7
    cr
    wcel
    #
    @25
    @3
    @25
    @3
    cc
    wcel
    #
    @3
    cc0
    wne
    #
    @25
    @24
    @32
    @33
    wa
    wph
    @24
    simpr
    @3
    cc
    cc0
    eldifsn
    sylib
    #
    simpld
    #
    @25
    @32
    @33
    @34
    simprd
    #
    absrpcld
    #
    crp
    cr
    @4
    @6
    cr
    crp
    @5
    wf1o
    #
    crp
    cr
    @6
    wf1o
    crp
    cr
    @6
    wf
    reeff1o
    cr
    crp
    @5
    f1ocnv
    crp
    cr
    @6
    f1of
    mp2b
    ffvelrni
    syl
    #
    recnd
    #
    @25
    ci
    cc
    wcel
    #
    @10
    cc
    wcel
    @11
    cc
    wcel
    #
    ax-icn
    @25
    @10
    @25
    cD
    cr
    @10
    wph
    cD
    cr
    wss
    @24
    eff1olem.3
    adantr
    @25
    cabs
    ccnv
    c1
    csn
    cima
    #
    cD
    @8
    @9
    wph
    @43
    cD
    @9
    wf
    #
    @24
    wph
    cD
    @43
    cF
    wf1o
    #
    @43
    cD
    @9
    wf1o
    @44
    wph
    vx
    vy
    vz
    vw
    @43
    cD
    csin
    cpi
    c2
    cdiv
    co
    #
    cneg
    @46
    cicc
    co
    cres
    #
    cF
    eff1olem.1
    @43
    eqid
    eff1olem.3
    eff1olem.4
    eff1olem.5
    @47
    eqid
    efif1olem4
    #
    cD
    @43
    cF
    f1ocnv
    @43
    cD
    @9
    f1of
    3syl
    adantr
    @25
    @8
    cc
    wcel
    #
    @8
    cabs
    cfv
    #
    c1
    wceq
    #
    @8
    @43
    wcel
    #
    @25
    @3
    @4
    @35
    @25
    @4
    @25
    @3
    @35
    abscld
    recnd
    #
    @25
    @3
    @35
    @36
    absne0d
    #
    divcld
    @25
    @50
    @4
    @4
    cabs
    cfv
    #
    cdiv
    co
    @4
    @4
    cdiv
    co
    c1
    @25
    @3
    @4
    @35
    @53
    @54
    absdivd
    @25
    @55
    @4
    @4
    cdiv
    @25
    @32
    @55
    @4
    wceq
    @35
    @3
    absidm
    syl
    oveq2d
    @25
    @4
    @53
    @54
    dividd
    3eqtrd
    cc
    cr
    cabs
    wf
    cabs
    cc
    wfn
    @52
    @49
    @51
    wa
    wb
    absf
    cc
    cr
    cabs
    ffn
    cc
    c1
    @8
    cabs
    fniniseg
    mp2b
    sylanbrc
    #
    ffvelrnd
    #
    sseldd
    #
    recnd
    ci
    @10
    mulcl
    sylancr
    #
    addcld
    @25
    @27
    @10
    cD
    @25
    @7
    @10
    @39
    @58
    crimd
    @57
    eqeltrd
    cc
    cr
    cim
    wf
    #
    cim
    cc
    wfn
    #
    @29
    @26
    @28
    wa
    wb
    imf
    cc
    cr
    cim
    ffn
    #
    cc
    @12
    cD
    cim
    elpreima
    mp2b
    sylanbrc
    eff1olem.2
    syl6eleqr
    wph
    @20
    @24
    wa
    wa
    #
    @1
    @12
    wceq
    #
    @3
    @2
    wceq
    #
    @63
    @65
    @64
    @3
    @12
    ce
    cfv
    #
    wceq
    #
    wph
    @24
    @67
    @20
    @25
    @66
    @7
    ce
    cfv
    #
    @11
    ce
    cfv
    #
    cmul
    co
    #
    @4
    @8
    cmul
    co
    @3
    @25
    @7
    cc
    wcel
    @42
    @66
    @70
    wceq
    @40
    @59
    @7
    @11
    efadd
    syl2anc
    @25
    @68
    @4
    @69
    @8
    cmul
    @25
    @7
    @5
    cfv
    #
    @68
    @4
    @25
    @31
    @71
    @68
    wceq
    @39
    @7
    cr
    ce
    fvres
    syl
    @25
    @38
    @30
    @71
    @4
    wceq
    reeff1o
    @37
    cr
    crp
    @4
    @5
    f1ocnvfv2
    sylancr
    eqtr3d
    @25
    @10
    cF
    cfv
    #
    @69
    @8
    @25
    @10
    cD
    wcel
    @72
    @69
    wceq
    @57
    vz
    @10
    ci
    vz
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    @69
    cD
    cF
    @73
    @10
    wceq
    @74
    @11
    ce
    @73
    @10
    ci
    cmul
    oveq2
    fveq2d
    cF
    vw
    cD
    ci
    vw
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmpt
    vz
    cD
    @75
    cmpt
    eff1olem.1
    vw
    vz
    cD
    @78
    @75
    @76
    @73
    wceq
    @77
    @74
    ce
    @76
    @73
    ci
    cmul
    oveq2
    fveq2d
    cbvmptv
    eqtri
    @11
    ce
    fvex
    fvmpt
    syl
    @25
    @45
    @52
    @72
    @8
    wceq
    wph
    @45
    @24
    @48
    adantr
    @56
    cD
    @43
    @8
    cF
    f1ocnvfv2
    syl2anc
    eqtr3d
    oveq12d
    @25
    @3
    @4
    @35
    @53
    @54
    divcan2d
    3eqtrrd
    adantrl
    @64
    @2
    @66
    @3
    @1
    @12
    ce
    fveq2
    eqeq2d
    syl5ibrcom
    wph
    @20
    @65
    @64
    wi
    @24
    wph
    @20
    wa
    #
    @64
    @65
    @1
    @2
    cabs
    cfv
    #
    @6
    cfv
    #
    ci
    @2
    @80
    cdiv
    co
    #
    @9
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    @79
    @1
    @1
    cre
    cfv
    #
    ci
    @1
    cim
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @85
    @79
    @1
    @20
    @22
    wph
    @23
    adantl
    #
    replimd
    #
    @79
    @81
    @86
    @84
    @88
    caddc
    @79
    @81
    @86
    @5
    cfv
    #
    @6
    cfv
    #
    @86
    @79
    @80
    @92
    @6
    @79
    @80
    @86
    ce
    cfv
    #
    @92
    @79
    @22
    @80
    @94
    wceq
    @90
    @1
    absef
    syl
    #
    @79
    @86
    cr
    wcel
    #
    @92
    @94
    wceq
    @79
    @1
    @90
    recld
    #
    @86
    cr
    ce
    fvres
    syl
    eqtr4d
    fveq2d
    @79
    @38
    @96
    @93
    @86
    wceq
    reeff1o
    @97
    cr
    crp
    @86
    @5
    f1ocnvfv1
    sylancr
    eqtrd
    @79
    @83
    @87
    ci
    cmul
    @79
    @83
    @87
    cF
    cfv
    #
    @9
    cfv
    #
    @87
    @79
    @82
    @98
    @9
    @79
    @94
    @88
    ce
    cfv
    #
    cmul
    co
    #
    @94
    cdiv
    co
    @100
    @82
    @98
    @79
    @100
    @94
    @79
    @88
    cc
    wcel
    #
    @100
    cc
    wcel
    @79
    @41
    @87
    cc
    wcel
    @102
    ax-icn
    @79
    @87
    @79
    @1
    @90
    imcld
    recnd
    ci
    @87
    mulcl
    sylancr
    #
    @88
    efcl
    syl
    @79
    @86
    cc
    wcel
    #
    @94
    cc
    wcel
    @79
    @86
    @97
    recnd
    #
    @86
    efcl
    syl
    @79
    @104
    @94
    cc0
    wne
    @105
    @86
    efne0
    syl
    divcan3d
    @79
    @2
    @101
    @80
    @94
    cdiv
    @79
    @2
    @89
    ce
    cfv
    #
    @101
    @79
    @1
    @89
    ce
    @91
    fveq2d
    @79
    @104
    @102
    @106
    @101
    wceq
    @105
    @103
    @86
    @88
    efadd
    syl2anc
    eqtrd
    @95
    oveq12d
    @79
    @87
    cD
    wcel
    #
    @98
    @100
    wceq
    @20
    @107
    wph
    @107
    @1
    @16
    cS
    @1
    @16
    wcel
    #
    @22
    @107
    @60
    @61
    @108
    @22
    @107
    wa
    wb
    imf
    @62
    cc
    @1
    cD
    cim
    elpreima
    mp2b
    simprbi
    eff1olem.2
    eleq2s
    #
    adantl
    vw
    @87
    @78
    @100
    cD
    cF
    @76
    @87
    wceq
    @77
    @88
    ce
    @76
    @87
    ci
    cmul
    oveq2
    fveq2d
    eff1olem.1
    @88
    ce
    fvex
    fvmpt
    syl
    3eqtr4d
    fveq2d
    wph
    @45
    @107
    @99
    @87
    wceq
    @20
    @48
    @109
    cD
    @43
    @87
    cF
    f1ocnvfv1
    syl2an
    eqtrd
    oveq2d
    oveq12d
    eqtr4d
    @65
    @12
    @85
    @1
    @65
    @7
    @81
    @11
    @84
    caddc
    @65
    @4
    @80
    @6
    @3
    @2
    cabs
    fveq2
    #
    fveq2d
    @65
    @10
    @83
    ci
    cmul
    @65
    @8
    @82
    @9
    @65
    @3
    @2
    @4
    @80
    cdiv
    @65
    id
    @110
    oveq12d
    fveq2d
    oveq2d
    oveq12d
    eqeq2d
    syl5ibrcom
    adantrr
    impbid
    f1o2d
end
