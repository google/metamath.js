include "ctop.mm"
include "wcel.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wrex.mm"
include "cuni.mm"
include "wral.mm"
include "cpconn.mm"
include "crest.mm"
include "cvv.mm"
include "cnfldtop.mm"
include "cc.mm"
include "wss.mm"
include "cnex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "resttop.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "cicc.mm"
include "cmul.mm"
include "cmin.mm"
include "caddc.mm"
include "cmpt.mm"
include "dfii3.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "cr.mm"
include "unitssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "cnmptid.mm"
include "adantr.mm"
include "simprr.mm"
include "sseldd.mm"
include "cnmptc.mm"
include "ctx.mm"
include "mulcn.mm"
include "cnmpt12f.mm"
include "1cnd.mm"
include "subcn.mm"
include "simprl.mm"
include "addcn.mm"
include "cnmpt1res.mm"
include "crn.mm"
include "wb.mm"
include "wf.mm"
include "wi.mm"
include "3exp2.mm"
include "com23.mm"
include "imp42.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "oveq2i.mm"
include "syl6eleqr.mm"
include "0elunit.mm"
include "oveq1.mm"
include "oveq2.mm"
include "1m0e1.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "mul02d.mm"
include "mulid2d.mm"
include "addid2d.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "1elunit.mm"
include "1m1e0.mm"
include "addid1d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ralrimivva.mm"
include "resttopon.mm"
include "toponuni.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "ispconn.mm"
include "sylanbrc.mm"

theorem cvxpconn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cS: class S
  let cJ: class J
  let cK: class K
  let vz: setvar z
  let vf: setvar f
  let vs: setvar s
  assume cvxpconn.1: |- ( ph -> S C_ CC )
  assume cvxpconn.2: |- ( ( ph /\ ( x e. S /\ y e. S /\ t e. ( 0 [,] 1 ) ) ) -> ( ( t x. x ) + ( ( 1 - t ) x. y ) ) e. S )
  assume cvxpconn.3: |- J = ( TopOpen ` CCfld )
  assume cvxpconn.4: |- K = ( J |`t S )

  disjoint J t
  disjoint t x
  disjoint t y
  disjoint K t
  disjoint x y
  disjoint K x
  disjoint K y
  disjoint ph t
  disjoint ph x
  disjoint ph y
  disjoint S t
  disjoint S x
  disjoint S y
  disjoint t z
  disjoint J z
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint K f
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint K s
  disjoint x z
  disjoint y z
  disjoint K z
  disjoint f ph
  disjoint ph s
  disjoint ph z
  disjoint S z
  assert |- ( ph -> K e. PConn )

  proof
    wph
    cK
    ctop
    wcel
    cc0
    vf
    cv
    #
    cfv
    #
    vy
    cv
    #
    wceq
    #
    c1
    @0
    cfv
    #
    vx
    cv
    #
    wceq
    #
    wa
    #
    vf
    cii
    cK
    ccn
    co
    #
    wrex
    #
    vx
    cK
    cuni
    #
    wral
    #
    vy
    @10
    wral
    #
    cK
    cpconn
    wcel
    wph
    cK
    cJ
    cS
    crest
    co
    #
    ctop
    cvxpconn.4
    wph
    cJ
    ctop
    wcel
    cS
    cvv
    wcel
    #
    @13
    ctop
    wcel
    cJ
    cvxpconn.3
    cnfldtop
    wph
    cS
    cc
    wss
    #
    cc
    cvv
    wcel
    @14
    cvxpconn.1
    cnex
    cS
    cc
    cvv
    ssexg
    sylancl
    cS
    cJ
    cvv
    resttop
    sylancr
    syl5eqel
    wph
    @9
    vx
    cS
    wral
    #
    vy
    cS
    wral
    @12
    wph
    @9
    vy
    vx
    cS
    cS
    wph
    @2
    cS
    wcel
    #
    @5
    cS
    wcel
    #
    wa
    #
    wa
    #
    vt
    cc0
    c1
    cicc
    co
    #
    vt
    cv
    #
    @5
    cmul
    co
    #
    c1
    @22
    cmin
    co
    #
    @2
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    @8
    wcel
    cc0
    @27
    cfv
    #
    @2
    wceq
    #
    c1
    @27
    cfv
    #
    @5
    wceq
    #
    @9
    @20
    @27
    cii
    @13
    ccn
    co
    #
    @8
    @20
    @27
    cii
    cJ
    ccn
    co
    wcel
    #
    @27
    @32
    wcel
    #
    @20
    vt
    @26
    cJ
    cii
    cJ
    cc
    @21
    cJ
    cvxpconn.3
    dfii3
    cJ
    cc
    ctopon
    cfv
    wcel
    #
    @20
    cJ
    cvxpconn.3
    cnfldtopon
    #
    a1i
    #
    @21
    cc
    wss
    @20
    @21
    cr
    cc
    unitssre
    ax-resscn
    sstri
    a1i
    @20
    vt
    @23
    @25
    caddc
    cJ
    cJ
    cJ
    cJ
    cc
    @37
    @20
    vt
    @22
    @5
    cmul
    cJ
    cJ
    cJ
    cJ
    cc
    @37
    @20
    vt
    cJ
    cc
    @37
    cnmptid
    #
    @20
    vt
    @5
    cJ
    cJ
    cc
    cc
    @37
    @37
    @20
    cS
    cc
    @5
    wph
    @15
    @19
    cvxpconn.1
    adantr
    #
    wph
    @17
    @18
    simprr
    sseldd
    #
    cnmptc
    cmul
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    #
    wcel
    @20
    cJ
    cvxpconn.3
    mulcn
    a1i
    #
    cnmpt12f
    @20
    vt
    @24
    @2
    cmul
    cJ
    cJ
    cJ
    cJ
    cc
    @37
    @20
    vt
    c1
    @22
    cmin
    cJ
    cJ
    cJ
    cJ
    cc
    @37
    @20
    vt
    c1
    cJ
    cJ
    cc
    cc
    @37
    @37
    @20
    1cnd
    cnmptc
    @38
    cmin
    @41
    wcel
    @20
    cJ
    cvxpconn.3
    subcn
    a1i
    cnmpt12f
    @20
    vt
    @2
    cJ
    cJ
    cc
    cc
    @37
    @37
    @20
    cS
    cc
    @2
    @39
    wph
    @17
    @18
    simprl
    sseldd
    #
    cnmptc
    @42
    cnmpt12f
    caddc
    @41
    wcel
    @20
    cJ
    cvxpconn.3
    addcn
    a1i
    cnmpt12f
    cnmpt1res
    @20
    @35
    @27
    crn
    cS
    wss
    #
    @15
    @33
    @34
    wb
    @37
    @20
    @21
    cS
    @27
    wf
    @44
    @20
    vt
    @21
    @26
    cS
    @27
    wph
    @17
    @18
    @22
    @21
    wcel
    #
    @26
    cS
    wcel
    #
    wph
    @18
    @17
    @45
    @46
    wi
    wph
    @18
    @17
    @45
    @46
    cvxpconn.2
    3exp2
    com23
    imp42
    @27
    eqid
    #
    fmptd
    @21
    cS
    @27
    frn
    syl
    @39
    cS
    @27
    cii
    cJ
    cc
    cnrest2
    syl3anc
    mpbid
    cK
    @13
    cii
    ccn
    cvxpconn.4
    oveq2i
    syl6eleqr
    @20
    @28
    cc0
    @5
    cmul
    co
    #
    c1
    @2
    cmul
    co
    #
    caddc
    co
    #
    @2
    cc0
    @21
    wcel
    @28
    @50
    wceq
    0elunit
    vt
    cc0
    @26
    @50
    @21
    @27
    @22
    cc0
    wceq
    #
    @23
    @48
    @25
    @49
    caddc
    @22
    cc0
    @5
    cmul
    oveq1
    @51
    @24
    c1
    @2
    cmul
    @51
    @24
    c1
    cc0
    cmin
    co
    c1
    @22
    cc0
    c1
    cmin
    oveq2
    1m0e1
    syl6eq
    oveq1d
    oveq12d
    @47
    @48
    @49
    caddc
    ovex
    fvmpt
    ax-mp
    @20
    @50
    cc0
    @2
    caddc
    co
    @2
    @20
    @48
    cc0
    @49
    @2
    caddc
    @20
    @5
    @40
    mul02d
    @20
    @2
    @43
    mulid2d
    oveq12d
    @20
    @2
    @43
    addid2d
    eqtrd
    syl5eq
    @20
    @30
    c1
    @5
    cmul
    co
    #
    cc0
    @2
    cmul
    co
    #
    caddc
    co
    #
    @5
    c1
    @21
    wcel
    @30
    @54
    wceq
    1elunit
    vt
    c1
    @26
    @54
    @21
    @27
    @22
    c1
    wceq
    #
    @23
    @52
    @25
    @53
    caddc
    @22
    c1
    @5
    cmul
    oveq1
    @55
    @24
    cc0
    @2
    cmul
    @55
    @24
    c1
    c1
    cmin
    co
    cc0
    @22
    c1
    c1
    cmin
    oveq2
    1m1e0
    syl6eq
    oveq1d
    oveq12d
    @47
    @52
    @53
    caddc
    ovex
    fvmpt
    ax-mp
    @20
    @54
    @5
    cc0
    caddc
    co
    @5
    @20
    @52
    @5
    @53
    cc0
    caddc
    @20
    @5
    @40
    mulid2d
    @20
    @2
    @43
    mul02d
    oveq12d
    @20
    @5
    @40
    addid1d
    eqtrd
    syl5eq
    @7
    @29
    @31
    wa
    vf
    @27
    @8
    @0
    @27
    wceq
    #
    @3
    @29
    @6
    @31
    @56
    @1
    @28
    @2
    cc0
    @0
    @27
    fveq1
    eqeq1d
    @56
    @4
    @30
    @5
    c1
    @0
    @27
    fveq1
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    ralrimivva
    wph
    @16
    @11
    vy
    cS
    @10
    wph
    cK
    cS
    ctopon
    cfv
    #
    wcel
    cS
    @10
    wceq
    wph
    cK
    @13
    @57
    cvxpconn.4
    wph
    @35
    @15
    @13
    @57
    wcel
    @36
    cvxpconn.1
    cS
    cJ
    cc
    resttopon
    sylancr
    syl5eqel
    cS
    cK
    toponuni
    syl
    #
    wph
    @9
    vx
    cS
    @10
    @58
    raleqdv
    raleqbidv
    mpbid
    vy
    vx
    vf
    cK
    @10
    @10
    eqid
    ispconn
    sylanbrc
end
