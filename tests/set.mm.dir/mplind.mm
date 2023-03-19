include "cin.mm"
include "inss1.mm"
include "crn.mm"
include "cmps.mm"
include "co.mm"
include "casp.mm"
include "cfv.mm"
include "casa.mm"
include "wcel.mm"
include "cbs.mm"
include "wss.mm"
include "cvv.mm"
include "eqid.mm"
include "psrassa.mm"
include "inss2.mm"
include "csubrg.mm"
include "ccrg.mm"
include "crg.mm"
include "crngring.mm"
include "syl.mm"
include "mplsubrg.mm"
include "subrgss.mm"
include "syl5ss.mm"
include "wfn.mm"
include "cv.mm"
include "wral.mm"
include "wf.mm"
include "mvrf2.mm"
include "ffn.mm"
include "ralrimiva.mm"
include "fnfvrnss.mm"
include "syl2anc.mm"
include "frn.mm"
include "ssind.mm"
include "aspss.mm"
include "syl3anc.mm"
include "mplbas2.mm"
include "syl6eqr.mm"
include "clss.mm"
include "wceq.mm"
include "csubg.mm"
include "cur.mm"
include "c0.mm"
include "wne.mm"
include "cminusg.mm"
include "wa.mm"
include "a1i.mm"
include "csca.mm"
include "crh.mm"
include "mplassa.mm"
include "asclrhm.mm"
include "rhm1.mm"
include "mplsca.mm"
include "eqeltrrd.mm"
include "ringidcl.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleqtrrd.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcva.mm"
include "assaring.mm"
include "elind.mm"
include "ne0i.mm"
include "sseli.mm"
include "anim12i.mm"
include "caovclg.mm"
include "sylan2.mm"
include "cgrp.mm"
include "clmod.mm"
include "assalmod.mm"
include "lmodgrp.mm"
include "adantr.mm"
include "simprl.mm"
include "sseldi.mm"
include "simprr.mm"
include "grpcl.mm"
include "anassrs.mm"
include "simpr.mm"
include "ringnegl.mm"
include "simpl.mm"
include "cghm.mm"
include "rhmghm.mm"
include "ghminv.mm"
include "eqtrd.mm"
include "ringgrp.mm"
include "grpinvcl.mm"
include "syl12anc.mm"
include "jca.mm"
include "w3a.mm"
include "wb.mm"
include "issubg2.mm"
include "mpbir3and.mm"
include "ringcl.mm"
include "ralrimivva.mm"
include "issubrg2.mm"
include "mplval2.mm"
include "subsubrg.mm"
include "simprbda.mm"
include "mpllss.mm"
include "cvsca.mm"
include "asclmul1.mm"
include "syldan.mm"
include "lmodvscl.mm"
include "islss4.mm"
include "mpbir2and.mm"
include "lsslss.mm"
include "syl21anc.mm"
include "aspid.mm"
include "3sstr3d.mm"
include "sseldd.mm"

theorem mplind
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vz: setvar z
  assume mplind.sk: |- K = ( Base ` R )
  assume mplind.sv: |- V = ( I mVar R )
  assume mplind.sy: |- Y = ( I mPoly R )
  assume mplind.sp: |- .+ = ( +g ` Y )
  assume mplind.st: |- .x. = ( .r ` Y )
  assume mplind.sc: |- C = ( algSc ` Y )
  assume mplind.sb: |- B = ( Base ` Y )
  assume mplind.p: |- ( ( ph /\ ( x e. H /\ y e. H ) ) -> ( x .+ y ) e. H )
  assume mplind.t: |- ( ( ph /\ ( x e. H /\ y e. H ) ) -> ( x .x. y ) e. H )
  assume mplind.s: |- ( ( ph /\ x e. K ) -> ( C ` x ) e. H )
  assume mplind.v: |- ( ( ph /\ x e. I ) -> ( V ` x ) e. H )
  assume mplind.x: |- ( ph -> X e. B )
  assume mplind.i: |- ( ph -> I e. _V )
  assume mplind.r: |- ( ph -> R e. CRing )

  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint I x
  disjoint ph x
  disjoint ph y
  disjoint H x
  disjoint H y
  disjoint K x
  disjoint .x. x
  disjoint .x. y
  disjoint V x
  disjoint Y x
  disjoint Y y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .+ w
  disjoint x z
  disjoint y z
  disjoint .+ z
  disjoint B w
  disjoint B z
  disjoint ph w
  disjoint ph z
  disjoint H w
  disjoint H z
  disjoint Y w
  disjoint Y z
  assert |- ( ph -> X e. H )

  proof
    wph
    cH
    cB
    cin
    #
    cH
    cX
    cH
    cB
    inss1
    #
    wph
    cB
    @0
    cX
    wph
    cV
    crn
    #
    cI
    cR
    cmps
    co
    #
    casp
    cfv
    #
    cfv
    #
    @0
    @4
    cfv
    #
    cB
    @0
    wph
    @3
    casa
    wcel
    #
    @0
    @3
    cbs
    cfv
    #
    wss
    @2
    @0
    wss
    @5
    @6
    wss
    wph
    cR
    @3
    cI
    cvv
    @3
    eqid
    #
    mplind.i
    mplind.r
    psrassa
    #
    wph
    @0
    cB
    @8
    cH
    cB
    inss2
    #
    wph
    cB
    @3
    csubrg
    cfv
    #
    wcel
    #
    cB
    @8
    wss
    wph
    cY
    cR
    @3
    cB
    cI
    cvv
    @9
    mplind.sy
    mplind.sb
    mplind.i
    wph
    cR
    ccrg
    wcel
    #
    cR
    crg
    wcel
    mplind.r
    cR
    crngring
    syl
    #
    mplsubrg
    #
    cB
    @8
    @3
    @8
    eqid
    #
    subrgss
    syl
    syl5ss
    wph
    @2
    cH
    cB
    wph
    cV
    cI
    wfn
    #
    vx
    cv
    #
    cV
    cfv
    cH
    wcel
    #
    vx
    cI
    wral
    @2
    cH
    wss
    wph
    cI
    cB
    cV
    wf
    #
    @18
    wph
    cB
    cY
    cR
    cI
    cV
    cvv
    mplind.sy
    mplind.sv
    mplind.sb
    mplind.i
    @15
    mvrf2
    #
    cI
    cB
    cV
    ffn
    syl
    wph
    @20
    vx
    cI
    mplind.v
    ralrimiva
    vx
    cI
    cH
    cV
    fnfvrnss
    syl2anc
    wph
    @21
    @2
    cB
    wss
    @22
    cI
    cB
    cV
    frn
    syl
    ssind
    @4
    @0
    @2
    @8
    @3
    @4
    eqid
    #
    @17
    aspss
    syl3anc
    wph
    @5
    cY
    cbs
    cfv
    cB
    wph
    @4
    cY
    cR
    @3
    cI
    cV
    cvv
    mplind.sy
    @9
    mplind.sv
    @23
    mplind.i
    mplind.r
    mplbas2
    mplind.sb
    syl6eqr
    wph
    @7
    @0
    @12
    wcel
    #
    @0
    @3
    clss
    cfv
    #
    wcel
    #
    @6
    @0
    wceq
    @10
    wph
    @13
    @0
    cY
    csubrg
    cfv
    wcel
    #
    @24
    @16
    wph
    @27
    @0
    cY
    csubg
    cfv
    wcel
    #
    cY
    cur
    cfv
    #
    @0
    wcel
    #
    @19
    vy
    cv
    #
    c.x
    co
    #
    @0
    wcel
    #
    vy
    @0
    wral
    vx
    @0
    wral
    #
    wph
    @28
    @0
    cB
    wss
    #
    @0
    c0
    wne
    #
    vz
    cv
    #
    vw
    cv
    #
    c.pl
    co
    #
    @0
    wcel
    #
    vw
    @0
    wral
    #
    @37
    cY
    cminusg
    cfv
    #
    cfv
    #
    @0
    wcel
    #
    wa
    #
    vz
    @0
    wral
    #
    @35
    wph
    @11
    a1i
    wph
    @30
    @36
    wph
    cH
    cB
    @29
    wph
    cY
    csca
    cfv
    #
    cur
    cfv
    #
    cC
    cfv
    #
    @29
    cH
    wph
    cC
    @47
    cY
    crh
    co
    wcel
    #
    @49
    @29
    wceq
    wph
    cY
    casa
    wcel
    #
    @50
    wph
    cI
    cvv
    wcel
    @14
    @51
    mplind.i
    mplind.r
    cY
    cR
    cI
    cvv
    mplind.sy
    mplassa
    syl2anc
    #
    cC
    @47
    cY
    mplind.sc
    @47
    eqid
    #
    asclrhm
    syl
    #
    @47
    cY
    @48
    cC
    @29
    @48
    eqid
    #
    @29
    eqid
    #
    rhm1
    syl
    #
    wph
    @48
    cK
    wcel
    @19
    cC
    cfv
    #
    cH
    wcel
    #
    vx
    cK
    wral
    #
    @49
    cH
    wcel
    #
    wph
    @48
    @47
    cbs
    cfv
    #
    cK
    wph
    @47
    crg
    wcel
    #
    @48
    @62
    wcel
    #
    wph
    cR
    @47
    crg
    wph
    cY
    cR
    cI
    cvv
    ccrg
    mplind.sy
    mplind.i
    mplind.r
    mplsca
    #
    @15
    eqeltrrd
    #
    @62
    @47
    @48
    @62
    eqid
    #
    @55
    ringidcl
    syl
    #
    wph
    cK
    cR
    cbs
    cfv
    @62
    mplind.sk
    wph
    cR
    @47
    cbs
    @65
    fveq2d
    syl5eq
    #
    eleqtrrd
    wph
    @59
    vx
    cK
    mplind.s
    ralrimiva
    #
    @59
    @61
    vx
    @48
    cK
    @19
    @48
    wceq
    @58
    @49
    cH
    @19
    @48
    cC
    fveq2
    eleq1d
    rspcva
    syl2anc
    eqeltrrd
    wph
    cY
    crg
    wcel
    #
    @29
    cB
    wcel
    wph
    @51
    @71
    @52
    cY
    assaring
    syl
    #
    cB
    cY
    @29
    mplind.sb
    @56
    ringidcl
    syl
    elind
    #
    @0
    @29
    ne0i
    syl
    wph
    @45
    vz
    @0
    wph
    @37
    @0
    wcel
    #
    wa
    #
    @41
    @44
    @75
    @40
    vw
    @0
    wph
    @74
    @38
    @0
    wcel
    #
    @40
    wph
    @74
    @76
    wa
    #
    wa
    #
    cH
    cB
    @39
    @77
    wph
    @37
    cH
    wcel
    #
    @38
    cH
    wcel
    #
    wa
    @39
    cH
    wcel
    @74
    @79
    @76
    @80
    @0
    cH
    @37
    @1
    sseli
    @0
    cH
    @38
    @1
    sseli
    anim12i
    wph
    vx
    vy
    @37
    @38
    cH
    cH
    cH
    c.pl
    mplind.p
    caovclg
    sylan2
    @78
    cY
    cgrp
    wcel
    #
    @37
    cB
    wcel
    #
    @38
    cB
    wcel
    #
    @39
    cB
    wcel
    wph
    @81
    @77
    wph
    cY
    clmod
    wcel
    #
    @81
    wph
    @51
    @84
    @52
    cY
    assalmod
    syl
    #
    cY
    lmodgrp
    syl
    #
    adantr
    @78
    @0
    cB
    @37
    @11
    wph
    @74
    @76
    simprl
    sseldi
    @78
    @0
    cB
    @38
    @11
    wph
    @74
    @76
    simprr
    sseldi
    cB
    c.pl
    cY
    @37
    @38
    mplind.sb
    mplind.sp
    grpcl
    syl3anc
    elind
    anassrs
    ralrimiva
    @75
    cH
    cB
    @43
    @75
    @29
    @42
    cfv
    #
    @37
    c.x
    co
    #
    @43
    cH
    @75
    cB
    cY
    c.x
    @29
    @42
    @37
    mplind.sb
    mplind.st
    @56
    @42
    eqid
    #
    wph
    @71
    @74
    @72
    adantr
    @75
    @0
    cB
    @37
    @11
    wph
    @74
    simpr
    #
    sseldi
    #
    ringnegl
    @75
    wph
    @87
    cH
    wcel
    #
    @79
    @88
    cH
    wcel
    wph
    @74
    simpl
    wph
    @92
    @74
    wph
    @48
    @47
    cminusg
    cfv
    #
    cfv
    #
    cC
    cfv
    #
    @87
    cH
    wph
    @95
    @49
    @42
    cfv
    #
    @87
    wph
    cC
    @47
    cY
    cghm
    co
    wcel
    #
    @64
    @95
    @96
    wceq
    wph
    @50
    @97
    @54
    @47
    cY
    cC
    rhmghm
    syl
    @68
    @62
    @47
    cY
    cC
    @93
    @42
    @48
    @67
    @93
    eqid
    #
    @89
    ghminv
    syl2anc
    wph
    @49
    @29
    @42
    @57
    fveq2d
    eqtrd
    wph
    @94
    cK
    wcel
    @60
    @95
    cH
    wcel
    #
    wph
    @94
    @62
    cK
    wph
    @47
    cgrp
    wcel
    #
    @64
    @94
    @62
    wcel
    wph
    @63
    @100
    @66
    @47
    ringgrp
    syl
    @68
    @62
    @47
    @93
    @48
    @67
    @98
    grpinvcl
    syl2anc
    @69
    eleqtrrd
    @70
    @59
    @99
    vx
    @94
    cK
    @19
    @94
    wceq
    @58
    @95
    cH
    @19
    @94
    cC
    fveq2
    eleq1d
    rspcva
    syl2anc
    eqeltrrd
    adantr
    @75
    @0
    cH
    @37
    @1
    @90
    sseldi
    wph
    vx
    vy
    @87
    @37
    cH
    cH
    cH
    c.x
    mplind.t
    caovclg
    syl12anc
    eqeltrrd
    @75
    @81
    @82
    @43
    cB
    wcel
    wph
    @81
    @74
    @86
    adantr
    @91
    cB
    cY
    @42
    @37
    mplind.sb
    @89
    grpinvcl
    syl2anc
    elind
    jca
    ralrimiva
    wph
    @81
    @28
    @35
    @36
    @46
    w3a
    wb
    @86
    vz
    vw
    cB
    c.pl
    @0
    cY
    @42
    mplind.sb
    mplind.sp
    @89
    issubg2
    syl
    mpbir3and
    #
    @73
    wph
    @33
    vx
    vy
    @0
    @0
    wph
    @19
    @0
    wcel
    #
    @31
    @0
    wcel
    #
    wa
    #
    wa
    #
    cH
    cB
    @32
    @104
    wph
    @19
    cH
    wcel
    #
    @31
    cH
    wcel
    #
    wa
    @32
    cH
    wcel
    @102
    @106
    @103
    @107
    @0
    cH
    @19
    @1
    sseli
    @0
    cH
    @31
    @1
    sseli
    anim12i
    mplind.t
    sylan2
    @105
    @71
    @19
    cB
    wcel
    @31
    cB
    wcel
    @32
    cB
    wcel
    wph
    @71
    @104
    @72
    adantr
    @105
    @0
    cB
    @19
    @11
    wph
    @102
    @103
    simprl
    sseldi
    @105
    @0
    cB
    @31
    @11
    wph
    @102
    @103
    simprr
    sseldi
    cB
    cY
    c.x
    @19
    @31
    mplind.sb
    mplind.st
    ringcl
    syl3anc
    elind
    ralrimivva
    wph
    @71
    @27
    @28
    @30
    @34
    w3a
    wb
    @72
    vx
    vy
    @0
    cB
    cY
    c.x
    @29
    mplind.sb
    @56
    mplind.st
    issubrg2
    syl
    mpbir3and
    @13
    @27
    @24
    @35
    cB
    @0
    @3
    cY
    cY
    cR
    @3
    cB
    cI
    mplind.sy
    @9
    mplind.sb
    mplval2
    #
    subsubrg
    simprbda
    syl2anc
    wph
    @3
    clmod
    wcel
    #
    cB
    @25
    wcel
    #
    @0
    cY
    clss
    cfv
    #
    wcel
    #
    @26
    wph
    @7
    @109
    @10
    @3
    assalmod
    syl
    wph
    cY
    cR
    @3
    cB
    cI
    cvv
    @9
    mplind.sy
    mplind.sb
    mplind.i
    @15
    mpllss
    wph
    @112
    @28
    @37
    @38
    cY
    cvsca
    cfv
    #
    co
    #
    @0
    wcel
    #
    vw
    @0
    wral
    vz
    @62
    wral
    #
    @101
    wph
    @115
    vz
    vw
    @62
    @0
    wph
    @37
    @62
    wcel
    #
    @76
    wa
    #
    wa
    #
    cH
    cB
    @114
    @119
    @37
    cC
    cfv
    #
    @38
    c.x
    co
    #
    @114
    cH
    @119
    @51
    @117
    @83
    @121
    @114
    wceq
    wph
    @51
    @118
    @52
    adantr
    wph
    @117
    @76
    simprl
    #
    @119
    @0
    cB
    @38
    @11
    wph
    @117
    @76
    simprr
    #
    sseldi
    #
    cC
    @37
    @113
    c.x
    @47
    @62
    cB
    cY
    @38
    mplind.sc
    @53
    @67
    mplind.sb
    mplind.st
    @113
    eqid
    #
    asclmul1
    syl3anc
    wph
    @118
    @120
    cH
    wcel
    #
    @80
    wa
    @121
    cH
    wcel
    @119
    @126
    @80
    @119
    @37
    cK
    wcel
    @60
    @126
    @119
    @37
    @62
    cK
    @122
    wph
    cK
    @62
    wceq
    @118
    @69
    adantr
    eleqtrrd
    wph
    @60
    @118
    @70
    adantr
    @59
    @126
    vx
    @37
    cK
    @19
    @37
    wceq
    @58
    @120
    cH
    @19
    @37
    cC
    fveq2
    eleq1d
    rspcva
    syl2anc
    @119
    @0
    cH
    @38
    @1
    @123
    sseldi
    jca
    wph
    vx
    vy
    @120
    @38
    cH
    cH
    cH
    c.x
    mplind.t
    caovclg
    syldan
    eqeltrrd
    @119
    @84
    @117
    @83
    @114
    cB
    wcel
    wph
    @84
    @118
    @85
    adantr
    @122
    @124
    @37
    @113
    @47
    @62
    cB
    cY
    @38
    mplind.sb
    @53
    @125
    @67
    lmodvscl
    syl3anc
    elind
    ralrimivva
    wph
    @84
    @112
    @28
    @116
    wa
    wb
    @85
    @62
    @111
    @113
    @0
    @47
    cB
    cY
    vz
    vw
    @53
    @67
    mplind.sb
    @125
    @111
    eqid
    #
    islss4
    syl
    mpbir2and
    @109
    @110
    wa
    @112
    @26
    @35
    @25
    @111
    cB
    @0
    @3
    cY
    @108
    @25
    eqid
    #
    @127
    lsslss
    simprbda
    syl21anc
    @4
    @0
    @25
    @8
    @3
    @23
    @17
    @128
    aspid
    syl3anc
    3sstr3d
    mplind.x
    sseldd
    sseldi
end
