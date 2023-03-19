include "ccnfld.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cun.mm"
include "cres.mm"
include "cgsu.mm"
include "cdiv.mm"
include "wcel.mm"
include "cfv.mm"
include "ccom.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "cr.mm"
include "cfn.mm"
include "cc0.mm"
include "cnfld0.mm"
include "crg.mm"
include "cabl.mm"
include "cnring.mm"
include "ringabl.mm"
include "mp1i.mm"
include "wss.mm"
include "unssad.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "csubrg.mm"
include "csubg.mm"
include "crefld.mm"
include "cdr.mm"
include "resubdrg.mm"
include "simpli.mm"
include "subrgsubg.mm"
include "wa.mm"
include "remulcl.mm"
include "adantl.mm"
include "cpnf.mm"
include "cico.mm"
include "wf.mm"
include "rge0ssre.mm"
include "fss.mm"
include "sylancl.mm"
include "fssd.mm"
include "inidm.mm"
include "off.mm"
include "fssresd.mm"
include "cvv.mm"
include "c0ex.mm"
include "a1i.mm"
include "fdmfifsupp.mm"
include "gsumsubgcl.mm"
include "recnd.mm"
include "cc.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "unssbd.mm"
include "vex.mm"
include "snss.mm"
include "sylibr.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "sseldd.mm"
include "mulcld.mm"
include "jensenlem1.mm"
include "rpred.mm"
include "elrege0.mm"
include "simplbi.mm"
include "syl.mm"
include "readdcld.mm"
include "eqeltrd.mm"
include "0red.mm"
include "rpgt0d.mm"
include "simprbi.mm"
include "addge01d.mm"
include "mpbid.mm"
include "breqtrrd.mm"
include "ltletrd.mm"
include "gt0ne0d.mm"
include "divdird.mm"
include "cmpt.mm"
include "cnfldbas.mm"
include "cnfldadd.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "sselda.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "adantr.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "gsumunsn.mm"
include "feqmptd.mm"
include "offval2.mm"
include "reseq1d.mm"
include "resmptd.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "rpne0d.mm"
include "dmdcand.mm"
include "divsubdird.mm"
include "pncan2d.mm"
include "dividd.mm"
include "3eqtr3rd.mm"
include "div23d.mm"
include "eqtr4d.mm"
include "cicc.mm"
include "w3a.mm"
include "redivcld.mm"
include "clt.mm"
include "rpge0d.mm"
include "divge0.mm"
include "syl22anc.mm"
include "mulid1d.mm"
include "wb.mm"
include "1red.mm"
include "ledivmul.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "0re.mm"
include "1re.mm"
include "elicc2i.mm"
include "syl3anbrc.mm"
include "3jca.mm"
include "cvxcl.mm"
include "mpdan.mm"
include "remulcld.mm"
include "fco.mm"
include "resubcl.mm"
include "sylancr.mm"
include "wi.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "oveq1.mm"
include "expcom.mm"
include "vtocl3ga.mm"
include "syl3anc.mm"
include "pm2.43i.mm"
include "breqtrd.mm"
include "divgt0d.mm"
include "lemul2.mm"
include "leadd1dd.mm"
include "eqbrtrd.mm"
include "letrd.mm"
include "fmptco.mm"
include "3brtr4d.mm"
include "jca.mm"

theorem jensenlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let cT: class T
  let cF: class F
  let cL: class L
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  let vw: setvar w
  assume jensen.1: |- ( ph -> D C_ RR )
  assume jensen.2: |- ( ph -> F : D --> RR )
  assume jensen.3: |- ( ( ph /\ ( a e. D /\ b e. D ) ) -> ( a [,] b ) C_ D )
  assume jensen.4: |- ( ph -> A e. Fin )
  assume jensen.5: |- ( ph -> T : A --> ( 0 [,) +oo ) )
  assume jensen.6: |- ( ph -> X : A --> D )
  assume jensen.7: |- ( ph -> 0 < ( CCfld gsum T ) )
  assume jensen.8: |- ( ( ph /\ ( x e. D /\ y e. D /\ t e. ( 0 [,] 1 ) ) ) -> ( F ` ( ( t x. x ) + ( ( 1 - t ) x. y ) ) ) <_ ( ( t x. ( F ` x ) ) + ( ( 1 - t ) x. ( F ` y ) ) ) )
  assume jensenlem.1: |- ( ph -> -. z e. B )
  assume jensenlem.2: |- ( ph -> ( B u. { z } ) C_ A )
  assume jensenlem.s: |- S = ( CCfld gsum ( T |` B ) )
  assume jensenlem.l: |- L = ( CCfld gsum ( T |` ( B u. { z } ) ) )
  assume jensenlem.3: |- ( ph -> S e. RR+ )
  assume jensenlem.4: |- ( ph -> ( ( CCfld gsum ( ( T oF x. X ) |` B ) ) / S ) e. D )
  assume jensenlem.5: |- ( ph -> ( F ` ( ( CCfld gsum ( ( T oF x. X ) |` B ) ) / S ) ) <_ ( ( CCfld gsum ( ( T oF x. ( F o. X ) ) |` B ) ) / S ) )

  disjoint a b
  disjoint a t
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b t
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint D a
  disjoint D b
  disjoint D t
  disjoint D x
  disjoint D y
  disjoint a ph
  disjoint b ph
  disjoint ph t
  disjoint ph x
  disjoint ph y
  disjoint F a
  disjoint F b
  disjoint F t
  disjoint F x
  disjoint F y
  disjoint T a
  disjoint T b
  disjoint T t
  disjoint T x
  disjoint T y
  disjoint X a
  disjoint X b
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint a z
  disjoint B a
  disjoint b z
  disjoint B b
  disjoint t z
  disjoint B t
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint L t
  disjoint L x
  disjoint L y
  disjoint S a
  disjoint S b
  disjoint S t
  disjoint S x
  disjoint S y
  disjoint a c
  disjoint a k
  disjoint a w
  disjoint b c
  disjoint b k
  disjoint b w
  disjoint c k
  disjoint c t
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint k t
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint t w
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint D c
  disjoint D k
  disjoint D w
  disjoint c ph
  disjoint k ph
  disjoint ph w
  disjoint F c
  disjoint F k
  disjoint F w
  disjoint T c
  disjoint T k
  disjoint T w
  disjoint X c
  disjoint X k
  disjoint X w
  assert |- ( ph -> ( ( ( CCfld gsum ( ( T oF x. X ) |` ( B u. { z } ) ) ) / L ) e. D /\ ( F ` ( ( CCfld gsum ( ( T oF x. X ) |` ( B u. { z } ) ) ) / L ) ) <_ ( ( CCfld gsum ( ( T oF x. ( F o. X ) ) |` ( B u. { z } ) ) ) / L ) ) )

  proof
    wph
    ccnfld
    cT
    cX
    cmul
    cof
    #
    co
    #
    cB
    vz
    cv
    #
    csn
    #
    cun
    #
    cres
    #
    cgsu
    co
    #
    cL
    cdiv
    co
    #
    cD
    wcel
    @7
    cF
    cfv
    #
    ccnfld
    cT
    cF
    cX
    ccom
    #
    @0
    co
    #
    @4
    cres
    #
    cgsu
    co
    #
    cL
    cdiv
    co
    #
    cle
    wbr
    wph
    @7
    cS
    cL
    cdiv
    co
    #
    ccnfld
    @1
    cB
    cres
    #
    cgsu
    co
    #
    cS
    cdiv
    co
    #
    cmul
    co
    #
    c1
    @14
    cmin
    co
    #
    @2
    cX
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cD
    wph
    @16
    @2
    cT
    cfv
    #
    @20
    cmul
    co
    #
    caddc
    co
    #
    cL
    cdiv
    co
    @16
    cL
    cdiv
    co
    #
    @24
    cL
    cdiv
    co
    #
    caddc
    co
    @7
    @22
    wph
    @16
    @24
    cL
    wph
    @16
    wph
    cB
    cr
    @15
    ccnfld
    cfn
    cc0
    cnfld0
    ccnfld
    crg
    wcel
    #
    ccnfld
    cabl
    wcel
    wph
    cnring
    ccnfld
    ringabl
    mp1i
    #
    wph
    cA
    cfn
    wcel
    cB
    cA
    wss
    cB
    cfn
    wcel
    jensen.4
    wph
    cB
    @3
    cA
    jensenlem.2
    unssad
    #
    cA
    cB
    ssfi
    syl2anc
    #
    cr
    ccnfld
    csubrg
    cfv
    wcel
    #
    cr
    ccnfld
    csubg
    cfv
    wcel
    wph
    @32
    crefld
    cdr
    wcel
    resubdrg
    simpli
    cr
    ccnfld
    subrgsubg
    mp1i
    #
    wph
    cA
    cr
    cB
    @1
    wph
    vx
    vy
    cA
    cA
    cA
    cmul
    cr
    cr
    cr
    cT
    cX
    cfn
    cfn
    vx
    cv
    #
    cr
    wcel
    vy
    cv
    #
    cr
    wcel
    wa
    @34
    @35
    cmul
    co
    cr
    wcel
    wph
    @34
    @35
    remulcl
    adantl
    #
    wph
    cA
    cc0
    cpnf
    cico
    co
    #
    cT
    wf
    @37
    cr
    wss
    cA
    cr
    cT
    wf
    jensen.5
    rge0ssre
    cA
    @37
    cr
    cT
    fss
    sylancl
    #
    wph
    cA
    cD
    cr
    cX
    jensen.6
    jensen.1
    fssd
    jensen.4
    jensen.4
    cA
    inidm
    #
    off
    @30
    fssresd
    #
    wph
    cB
    cr
    @15
    cvv
    cc0
    @40
    @31
    cc0
    cvv
    wcel
    wph
    c0ex
    a1i
    #
    fdmfifsupp
    gsumsubgcl
    recnd
    #
    wph
    @23
    @20
    wph
    @37
    cc
    @23
    @37
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    #
    wph
    cA
    @37
    @2
    cT
    jensen.5
    wph
    @3
    cA
    wss
    @2
    cA
    wcel
    wph
    cB
    @3
    cA
    jensenlem.2
    unssbd
    @2
    cA
    vz
    vex
    snss
    sylibr
    #
    ffvelrnd
    #
    sseldi
    #
    wph
    @20
    wph
    cD
    cr
    @20
    jensen.1
    wph
    cA
    cD
    @2
    cX
    jensen.6
    @44
    ffvelrnd
    #
    sseldd
    recnd
    #
    mulcld
    #
    wph
    cL
    wph
    cL
    cS
    @23
    caddc
    co
    #
    cr
    wph
    vx
    vy
    vz
    vt
    cA
    cB
    cD
    cS
    cT
    cF
    cL
    cX
    va
    vb
    jensen.1
    jensen.2
    jensen.3
    jensen.4
    jensen.5
    jensen.6
    jensen.7
    jensen.8
    jensenlem.1
    jensenlem.2
    jensenlem.s
    jensenlem.l
    jensenlem1
    #
    wph
    cS
    @23
    wph
    cS
    jensenlem.3
    rpred
    #
    wph
    @23
    @37
    wcel
    #
    @23
    cr
    wcel
    #
    @45
    @53
    @54
    cc0
    @23
    cle
    wbr
    #
    @23
    elrege0
    #
    simplbi
    syl
    #
    readdcld
    eqeltrd
    #
    recnd
    #
    wph
    cL
    wph
    cc0
    cS
    cL
    wph
    0red
    @52
    @58
    wph
    cS
    jensenlem.3
    rpgt0d
    #
    wph
    cS
    @50
    cL
    cle
    wph
    @55
    cS
    @50
    cle
    wbr
    wph
    @53
    @55
    @45
    @53
    @54
    @55
    @56
    simprbi
    syl
    wph
    cS
    @23
    @52
    @57
    addge01d
    mpbid
    @51
    breqtrrd
    #
    ltletrd
    #
    gt0ne0d
    #
    divdird
    wph
    @6
    @25
    cL
    cdiv
    wph
    ccnfld
    vx
    @4
    @34
    cT
    cfv
    #
    @34
    cX
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cgsu
    co
    ccnfld
    vx
    cB
    @66
    cmpt
    #
    cgsu
    co
    #
    @24
    caddc
    co
    @6
    @25
    wph
    cB
    cc
    caddc
    vx
    ccnfld
    @2
    cA
    @66
    @24
    cnfldbas
    cnfldadd
    @28
    ccnfld
    ccmn
    wcel
    wph
    cnring
    ccnfld
    ringcmn
    mp1i
    #
    @31
    wph
    @34
    cB
    wcel
    #
    wa
    #
    @64
    @65
    @72
    @37
    cc
    @64
    @43
    wph
    @71
    @34
    cA
    wcel
    #
    @64
    @37
    wcel
    wph
    cB
    cA
    @34
    @30
    sselda
    #
    wph
    cA
    @37
    @34
    cT
    jensen.5
    ffvelrnda
    #
    syldan
    sseldi
    @72
    @65
    @72
    cD
    cr
    @65
    wph
    cD
    cr
    wss
    @71
    jensen.1
    adantr
    wph
    @71
    @73
    @65
    cD
    wcel
    #
    @74
    wph
    cA
    cD
    @34
    cX
    jensen.6
    ffvelrnda
    #
    syldan
    sseldd
    recnd
    mulcld
    @44
    jensenlem.1
    @49
    @34
    @2
    wceq
    #
    @64
    @23
    @65
    @20
    cmul
    @34
    @2
    cT
    fveq2
    #
    @34
    @2
    cX
    fveq2
    #
    oveq12d
    gsumunsn
    wph
    @5
    @67
    ccnfld
    cgsu
    wph
    @5
    vx
    cA
    @66
    cmpt
    #
    @4
    cres
    @67
    wph
    @1
    @81
    @4
    wph
    vx
    cA
    @64
    @65
    cmul
    cT
    cX
    cfn
    @37
    cD
    jensen.4
    @75
    @77
    wph
    vx
    cA
    @37
    cT
    jensen.5
    feqmptd
    #
    wph
    vx
    cA
    cD
    cX
    jensen.6
    feqmptd
    #
    offval2
    #
    reseq1d
    wph
    vx
    cA
    @4
    @66
    jensenlem.2
    resmptd
    eqtrd
    oveq2d
    wph
    @16
    @69
    @24
    caddc
    wph
    @15
    @68
    ccnfld
    cgsu
    wph
    @15
    @81
    cB
    cres
    @68
    wph
    @1
    @81
    cB
    @84
    reseq1d
    wph
    vx
    cA
    cB
    @66
    @30
    resmptd
    eqtrd
    oveq2d
    oveq1d
    3eqtr4d
    oveq1d
    wph
    @18
    @26
    @21
    @27
    caddc
    wph
    @16
    cS
    cL
    @42
    wph
    cS
    @52
    recnd
    #
    @59
    wph
    cS
    jensenlem.3
    rpne0d
    #
    @63
    dmdcand
    wph
    @21
    @23
    cL
    cdiv
    co
    #
    @20
    cmul
    co
    @27
    wph
    @19
    @87
    @20
    cmul
    wph
    cL
    cS
    cmin
    co
    #
    cL
    cdiv
    co
    cL
    cL
    cdiv
    co
    #
    @14
    cmin
    co
    @87
    @19
    wph
    cL
    cS
    cL
    @59
    @85
    @59
    @63
    divsubdird
    wph
    @88
    @23
    cL
    cdiv
    wph
    @88
    @50
    cS
    cmin
    co
    @23
    wph
    cL
    @50
    cS
    cmin
    @51
    oveq1d
    wph
    cS
    @23
    @85
    @46
    pncan2d
    eqtrd
    oveq1d
    wph
    @89
    c1
    @14
    cmin
    wph
    cL
    @59
    @63
    dividd
    oveq1d
    3eqtr3rd
    #
    oveq1d
    wph
    @23
    @20
    cL
    @46
    @48
    @59
    @63
    div23d
    eqtr4d
    oveq12d
    3eqtr4d
    #
    wph
    @17
    cD
    wcel
    #
    @20
    cD
    wcel
    #
    @14
    cc0
    c1
    cicc
    co
    #
    wcel
    #
    w3a
    @22
    cD
    wcel
    wph
    @92
    @93
    @95
    jensenlem.4
    @47
    wph
    @14
    cr
    wcel
    #
    cc0
    @14
    cle
    wbr
    #
    @14
    c1
    cle
    wbr
    #
    @95
    wph
    cS
    cL
    @52
    @58
    @63
    redivcld
    #
    wph
    cS
    cr
    wcel
    #
    cc0
    cS
    cle
    wbr
    cL
    cr
    wcel
    #
    cc0
    cL
    clt
    wbr
    #
    @97
    @52
    wph
    cS
    jensenlem.3
    rpge0d
    @58
    @62
    cS
    cL
    divge0
    syl22anc
    wph
    @98
    cS
    cL
    c1
    cmul
    co
    #
    cle
    wbr
    #
    wph
    cS
    cL
    @103
    cle
    @61
    wph
    cL
    @59
    mulid1d
    breqtrrd
    wph
    @100
    c1
    cr
    wcel
    #
    @101
    @102
    @98
    @104
    wb
    @52
    wph
    1red
    @58
    @62
    cS
    c1
    cL
    ledivmul
    syl112anc
    mpbird
    cc0
    c1
    @14
    0re
    1re
    elicc2i
    syl3anbrc
    #
    3jca
    wph
    va
    vb
    cD
    @14
    @17
    @20
    jensen.1
    jensen.3
    cvxcl
    mpdan
    #
    eqeltrd
    wph
    @22
    cF
    cfv
    #
    @14
    ccnfld
    @10
    cB
    cres
    #
    cgsu
    co
    #
    cS
    cdiv
    co
    #
    cmul
    co
    #
    @19
    @20
    cF
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @8
    @13
    cle
    wph
    @108
    @14
    @17
    cF
    cfv
    #
    cmul
    co
    #
    @23
    @113
    cmul
    co
    #
    cL
    cdiv
    co
    #
    caddc
    co
    #
    @115
    wph
    cD
    cr
    @22
    cF
    jensen.2
    @107
    ffvelrnd
    wph
    @117
    @119
    wph
    @14
    @116
    @99
    wph
    cD
    cr
    @17
    cF
    jensen.2
    jensenlem.4
    ffvelrnd
    #
    remulcld
    #
    wph
    @118
    cL
    wph
    @23
    @113
    @57
    wph
    cD
    cr
    @20
    cF
    jensen.2
    @47
    ffvelrnd
    #
    remulcld
    #
    @58
    @63
    redivcld
    readdcld
    wph
    @112
    @114
    wph
    @14
    @111
    @99
    wph
    @110
    cS
    wph
    cB
    cr
    @109
    ccnfld
    cfn
    cc0
    cnfld0
    @29
    @31
    @33
    wph
    cA
    cr
    cB
    @10
    wph
    vx
    vy
    cA
    cA
    cA
    cmul
    cr
    cr
    cr
    cT
    @9
    cfn
    cfn
    @36
    @38
    wph
    cD
    cr
    cF
    wf
    cA
    cD
    cX
    wf
    cA
    cr
    @9
    wf
    jensen.2
    jensen.6
    cA
    cD
    cr
    cF
    cX
    fco
    syl2anc
    jensen.4
    jensen.4
    @39
    off
    @30
    fssresd
    #
    wph
    cB
    cr
    @109
    cvv
    cc0
    @125
    @31
    @41
    fdmfifsupp
    gsumsubgcl
    #
    @52
    @86
    redivcld
    #
    remulcld
    #
    wph
    @19
    @113
    wph
    @105
    @96
    @19
    cr
    wcel
    1re
    @99
    c1
    @14
    resubcl
    sylancr
    @123
    remulcld
    #
    readdcld
    wph
    @108
    @117
    @114
    caddc
    co
    #
    @120
    cle
    wph
    @108
    @130
    cle
    wbr
    #
    wph
    @92
    @93
    @95
    wph
    @131
    wi
    #
    jensenlem.4
    @47
    @106
    wph
    vt
    cv
    #
    @34
    cmul
    co
    #
    c1
    @133
    cmin
    co
    #
    @35
    cmul
    co
    #
    caddc
    co
    #
    cF
    cfv
    #
    @133
    @34
    cF
    cfv
    #
    cmul
    co
    #
    @135
    @35
    cF
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    wi
    wph
    @133
    @17
    cmul
    co
    #
    @136
    caddc
    co
    #
    cF
    cfv
    #
    @133
    @116
    cmul
    co
    #
    @142
    caddc
    co
    #
    cle
    wbr
    #
    wi
    wph
    @145
    @135
    @20
    cmul
    co
    #
    caddc
    co
    #
    cF
    cfv
    #
    @148
    @135
    @113
    cmul
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    wi
    @132
    vx
    vy
    vt
    @17
    @20
    @14
    cD
    cD
    @94
    @34
    @17
    wceq
    #
    @144
    @150
    wph
    @157
    @138
    @147
    @143
    @149
    cle
    @157
    @137
    @146
    cF
    @157
    @134
    @145
    @136
    caddc
    @34
    @17
    @133
    cmul
    oveq2
    oveq1d
    fveq2d
    @157
    @140
    @148
    @142
    caddc
    @157
    @139
    @116
    @133
    cmul
    @34
    @17
    cF
    fveq2
    oveq2d
    oveq1d
    breq12d
    imbi2d
    @35
    @20
    wceq
    #
    @150
    @156
    wph
    @158
    @147
    @153
    @149
    @155
    cle
    @158
    @146
    @152
    cF
    @158
    @136
    @151
    @145
    caddc
    @35
    @20
    @135
    cmul
    oveq2
    oveq2d
    fveq2d
    @158
    @142
    @154
    @148
    caddc
    @158
    @141
    @113
    @135
    cmul
    @35
    @20
    cF
    fveq2
    oveq2d
    oveq2d
    breq12d
    imbi2d
    @133
    @14
    wceq
    #
    @156
    @131
    wph
    @159
    @153
    @108
    @155
    @130
    cle
    @159
    @152
    @22
    cF
    @159
    @145
    @18
    @151
    @21
    caddc
    @133
    @14
    @17
    cmul
    oveq1
    @159
    @135
    @19
    @20
    cmul
    @133
    @14
    c1
    cmin
    oveq2
    #
    oveq1d
    oveq12d
    fveq2d
    @159
    @148
    @117
    @154
    @114
    caddc
    @133
    @14
    @116
    cmul
    oveq1
    @159
    @135
    @19
    @113
    cmul
    @160
    oveq1d
    oveq12d
    breq12d
    imbi2d
    wph
    @34
    cD
    wcel
    @35
    cD
    wcel
    @133
    @94
    wcel
    w3a
    @144
    jensen.8
    expcom
    vtocl3ga
    syl3anc
    pm2.43i
    wph
    @114
    @119
    @117
    caddc
    wph
    @114
    @87
    @113
    cmul
    co
    #
    @119
    wph
    @19
    @87
    @113
    cmul
    @90
    oveq1d
    #
    wph
    @23
    @113
    cL
    @46
    wph
    @113
    @123
    recnd
    @59
    @63
    div23d
    #
    eqtr4d
    #
    oveq2d
    breqtrd
    wph
    @120
    @130
    @115
    cle
    wph
    @119
    @114
    @117
    caddc
    wph
    @119
    @161
    @114
    @163
    @162
    eqtr4d
    oveq2d
    wph
    @117
    @112
    @114
    @122
    @128
    @129
    wph
    @116
    @111
    cle
    wbr
    #
    @117
    @112
    cle
    wbr
    #
    jensenlem.5
    wph
    @116
    cr
    wcel
    @111
    cr
    wcel
    @96
    cc0
    @14
    clt
    wbr
    @165
    @166
    wb
    @121
    @127
    @99
    wph
    cS
    cL
    @52
    @58
    @60
    @62
    divgt0d
    @116
    @111
    @14
    lemul2
    syl112anc
    mpbid
    leadd1dd
    eqbrtrd
    letrd
    wph
    @7
    @22
    cF
    @91
    fveq2d
    wph
    @110
    @118
    caddc
    co
    #
    cL
    cdiv
    co
    @110
    cL
    cdiv
    co
    #
    @119
    caddc
    co
    @13
    @115
    wph
    @110
    @118
    cL
    wph
    @110
    @126
    recnd
    #
    wph
    @118
    @124
    recnd
    #
    @59
    @63
    divdird
    wph
    @12
    @167
    cL
    cdiv
    wph
    ccnfld
    vx
    @4
    @64
    @65
    cF
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cgsu
    co
    ccnfld
    vx
    cB
    @172
    cmpt
    #
    cgsu
    co
    #
    @118
    caddc
    co
    @12
    @167
    wph
    cB
    cc
    caddc
    vx
    ccnfld
    @2
    cA
    @172
    @118
    cnfldbas
    cnfldadd
    @70
    @31
    wph
    @71
    @73
    @172
    cc
    wcel
    @74
    wph
    @73
    wa
    #
    @172
    @176
    @64
    @171
    @176
    @37
    cr
    @64
    rge0ssre
    @75
    sseldi
    wph
    @73
    @76
    @171
    cr
    wcel
    @77
    wph
    cD
    cr
    @65
    cF
    jensen.2
    ffvelrnda
    syldan
    #
    remulcld
    recnd
    syldan
    @44
    jensenlem.1
    @170
    @78
    @64
    @23
    @171
    @113
    cmul
    @79
    @78
    @65
    @20
    cF
    @80
    fveq2d
    oveq12d
    gsumunsn
    wph
    @11
    @173
    ccnfld
    cgsu
    wph
    @11
    vx
    cA
    @172
    cmpt
    #
    @4
    cres
    @173
    wph
    @10
    @178
    @4
    wph
    vx
    cA
    @64
    @171
    cmul
    cT
    @9
    cfn
    @37
    cr
    jensen.4
    @75
    @177
    @82
    wph
    vx
    vy
    cA
    cD
    @65
    @141
    @171
    cX
    cF
    @77
    @83
    wph
    vy
    cD
    cr
    cF
    jensen.2
    feqmptd
    @35
    @65
    cF
    fveq2
    fmptco
    offval2
    #
    reseq1d
    wph
    vx
    cA
    @4
    @172
    jensenlem.2
    resmptd
    eqtrd
    oveq2d
    wph
    @110
    @175
    @118
    caddc
    wph
    @109
    @174
    ccnfld
    cgsu
    wph
    @109
    @178
    cB
    cres
    @174
    wph
    @10
    @178
    cB
    @179
    reseq1d
    wph
    vx
    cA
    cB
    @172
    @30
    resmptd
    eqtrd
    oveq2d
    oveq1d
    3eqtr4d
    oveq1d
    wph
    @112
    @168
    @114
    @119
    caddc
    wph
    @110
    cS
    cL
    @169
    @85
    @59
    @86
    @63
    dmdcand
    @164
    oveq12d
    3eqtr4d
    3brtr4d
    jca
end
