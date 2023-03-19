include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "c1.mm"
include "cfv.mm"
include "cdiv.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cmulr.mm"
include "cur.mm"
include "cn.mm"
include "dchrrcl.mm"
include "syl.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "wa.mm"
include "cc.mm"
include "wf.mm"
include "dchrf.mm"
include "unitss.mm"
include "sseli.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "wne.mm"
include "simpr.mm"
include "adantr.mm"
include "adantl.mm"
include "dchrn0.mm"
include "mpbird.mm"
include "reccld.mm"
include "cmul.mm"
include "1t1e1.mm"
include "eqcomi.mm"
include "a1i.mm"
include "cmgp.mm"
include "ccnfld.mm"
include "cmhm.mm"
include "dchrmhm.mm"
include "sseldi.mm"
include "simprl.mm"
include "simprr.mm"
include "eqid.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "cnfldmul.mm"
include "mhmlin.mm"
include "syl3anc.mm"
include "oveq12d.mm"
include "1cnd.mm"
include "ffvelrnd.mm"
include "divmuldivd.mm"
include "eqtr4d.mm"
include "ringidval.mm"
include "cnfld1.mm"
include "mhm0.mm"
include "1div1e1.mm"
include "syl6eq.mm"
include "dchrelbasd.mm"
include "syl5eqel.mm"
include "cof.mm"
include "dchrmul.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ovex.mm"
include "c0ex.mm"
include "ifex.mm"
include "ffvelrnda.mm"
include "feqmptd.mm"
include "offval2.mm"
include "ovif.mm"
include "biimpar.mm"
include "recid2d.mm"
include "ifeq1da.mm"
include "mul02d.mm"
include "ifeq2d.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "mpteq2dva.mm"
include "syl6reqr.mm"
include "jca.mm"

theorem dchrinvcl
  let wph: wff ph
  let cB: class B
  let cD: class D
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let vk: setvar k
  let cG: class G
  let cK: class K
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let cL: class L
  let cA: class A
  let cY: class Y
  assume dchrmhm.g: |- G = ( DChr ` N )
  assume dchrmhm.z: |- Z = ( Z/nZ ` N )
  assume dchrmhm.b: |- D = ( Base ` G )
  assume dchrn0.b: |- B = ( Base ` Z )
  assume dchrn0.u: |- U = ( Unit ` Z )
  assume dchr1cl.o: |- .1. = ( k e. B |-> if ( k e. U , 1 , 0 ) )
  assume dchrmulid2.t: |- .x. = ( +g ` G )
  assume dchrmulid2.x: |- ( ph -> X e. D )
  assume dchrinvcl.n: |- K = ( k e. B |-> if ( k e. U , ( 1 / ( X ` k ) ) , 0 ) )

  disjoint B k
  disjoint U k
  disjoint N k
  disjoint k ph
  disjoint X k
  disjoint Z k
  disjoint x y
  disjoint .1. x
  disjoint .1. y
  disjoint k x
  disjoint k y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint U x
  disjoint U y
  disjoint A x
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint Z x
  disjoint Z y
  disjoint D x
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( K e. D /\ ( K .x. X ) = .1. ) )

  proof
    wph
    cK
    cD
    wcel
    cK
    cX
    c.x
    co
    #
    c.1
    wceq
    wph
    cK
    vk
    cB
    vk
    cv
    #
    cU
    wcel
    #
    c1
    @1
    cX
    cfv
    #
    cdiv
    co
    #
    cc0
    cif
    #
    cmpt
    #
    cD
    dchrinvcl.n
    wph
    vx
    vy
    c1
    vx
    cv
    #
    cX
    cfv
    #
    cdiv
    co
    #
    cB
    c1
    vy
    cv
    #
    cX
    cfv
    #
    cdiv
    co
    #
    cD
    cU
    vk
    c1
    @7
    @10
    cZ
    cmulr
    cfv
    #
    co
    #
    cX
    cfv
    #
    cdiv
    co
    #
    cG
    cN
    @4
    c1
    cZ
    cur
    cfv
    #
    cX
    cfv
    #
    cdiv
    co
    #
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrn0.b
    dchrn0.u
    wph
    cX
    cD
    wcel
    #
    cN
    cn
    wcel
    dchrmulid2.x
    cD
    cG
    cN
    cX
    dchrmhm.g
    dchrmhm.b
    dchrrcl
    syl
    dchrmhm.b
    @1
    @7
    wceq
    @3
    @8
    c1
    cdiv
    @1
    @7
    cX
    fveq2
    oveq2d
    @1
    @10
    wceq
    @3
    @11
    c1
    cdiv
    @1
    @10
    cX
    fveq2
    oveq2d
    @1
    @14
    wceq
    @3
    @15
    c1
    cdiv
    @1
    @14
    cX
    fveq2
    oveq2d
    @1
    @17
    wceq
    @3
    @18
    c1
    cdiv
    @1
    @17
    cX
    fveq2
    oveq2d
    wph
    @2
    wa
    #
    @3
    wph
    cB
    cc
    cX
    wf
    #
    @1
    cB
    wcel
    #
    @3
    cc
    wcel
    #
    @2
    wph
    cB
    cD
    cG
    cN
    cX
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrmhm.b
    dchrn0.b
    dchrmulid2.x
    dchrf
    #
    cU
    cB
    @1
    cB
    cZ
    cU
    dchrn0.b
    dchrn0.u
    unitss
    #
    sseli
    #
    cB
    cc
    @1
    cX
    ffvelrn
    syl2an
    @21
    @3
    cc0
    wne
    #
    @2
    wph
    @2
    simpr
    @21
    @1
    cB
    cD
    cU
    cG
    cN
    cX
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrmhm.b
    dchrn0.b
    dchrn0.u
    wph
    @20
    @2
    dchrmulid2.x
    adantr
    @2
    @23
    wph
    @27
    adantl
    dchrn0
    mpbird
    reccld
    wph
    @7
    cU
    wcel
    #
    @10
    cU
    wcel
    #
    wa
    #
    wa
    #
    @16
    c1
    c1
    cmul
    co
    #
    @8
    @11
    cmul
    co
    #
    cdiv
    co
    @9
    @12
    cmul
    co
    @32
    c1
    @33
    @15
    @34
    cdiv
    c1
    @33
    wceq
    @32
    @33
    c1
    1t1e1
    eqcomi
    a1i
    @32
    cX
    cZ
    cmgp
    cfv
    #
    ccnfld
    cmgp
    cfv
    #
    cmhm
    co
    #
    wcel
    #
    @7
    cB
    wcel
    @10
    cB
    wcel
    @15
    @34
    wceq
    @32
    cD
    @37
    cX
    cD
    cG
    cN
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrmhm.b
    dchrmhm
    #
    wph
    @20
    @31
    dchrmulid2.x
    adantr
    #
    sseldi
    @32
    cU
    cB
    @7
    @26
    wph
    @29
    @30
    simprl
    #
    sseldi
    #
    @32
    cU
    cB
    @10
    @26
    wph
    @29
    @30
    simprr
    #
    sseldi
    #
    cB
    @13
    cmul
    @35
    @36
    cX
    @7
    @10
    cB
    cZ
    @35
    @35
    eqid
    #
    dchrn0.b
    mgpbas
    cZ
    @13
    @35
    @45
    @13
    eqid
    mgpplusg
    ccnfld
    cmul
    @36
    @36
    eqid
    #
    cnfldmul
    mgpplusg
    mhmlin
    syl3anc
    oveq12d
    @32
    c1
    @8
    c1
    @11
    @32
    1cnd
    #
    @32
    cB
    cc
    @7
    cX
    wph
    @22
    @31
    @25
    adantr
    #
    @42
    ffvelrnd
    @47
    @32
    cB
    cc
    @10
    cX
    @48
    @44
    ffvelrnd
    @32
    @8
    cc0
    wne
    @29
    @41
    @32
    @7
    cB
    cD
    cU
    cG
    cN
    cX
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrmhm.b
    dchrn0.b
    dchrn0.u
    @40
    @42
    dchrn0
    mpbird
    @32
    @11
    cc0
    wne
    @30
    @43
    @32
    @10
    cB
    cD
    cU
    cG
    cN
    cX
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrmhm.b
    dchrn0.b
    dchrn0.u
    @40
    @44
    dchrn0
    mpbird
    divmuldivd
    eqtr4d
    wph
    @19
    c1
    c1
    cdiv
    co
    c1
    wph
    @18
    c1
    c1
    cdiv
    wph
    @38
    @18
    c1
    wceq
    wph
    cD
    @37
    cX
    @39
    dchrmulid2.x
    sseldi
    @35
    @36
    cX
    c1
    @17
    cZ
    @17
    @35
    @45
    @17
    eqid
    ringidval
    ccnfld
    c1
    @36
    @46
    cnfld1
    ringidval
    mhm0
    syl
    oveq2d
    1div1e1
    syl6eq
    dchrelbasd
    syl5eqel
    #
    wph
    @0
    cK
    cX
    cmul
    cof
    co
    #
    c.1
    wph
    cD
    c.x
    cG
    cN
    cK
    cX
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrmhm.b
    dchrmulid2.t
    @49
    dchrmulid2.x
    dchrmul
    wph
    @50
    vk
    cB
    @5
    @3
    cmul
    co
    #
    cmpt
    #
    c.1
    wph
    vk
    cB
    @5
    @3
    cmul
    cK
    cX
    cvv
    cvv
    cc
    cB
    cvv
    wcel
    wph
    cB
    cZ
    cbs
    cfv
    cvv
    dchrn0.b
    cZ
    cbs
    fvex
    eqeltri
    a1i
    @5
    cvv
    wcel
    wph
    @23
    wa
    #
    @2
    @4
    cc0
    c1
    @3
    cdiv
    ovex
    c0ex
    ifex
    a1i
    wph
    cB
    cc
    @1
    cX
    @25
    ffvelrnda
    #
    cK
    @6
    wceq
    wph
    dchrinvcl.n
    a1i
    wph
    vk
    cB
    cc
    cX
    @25
    feqmptd
    offval2
    wph
    @52
    vk
    cB
    @2
    c1
    cc0
    cif
    #
    cmpt
    c.1
    wph
    vk
    cB
    @51
    @55
    @53
    @51
    @2
    @4
    @3
    cmul
    co
    #
    cc0
    @3
    cmul
    co
    #
    cif
    #
    @55
    @2
    @4
    cc0
    @3
    cmul
    ovif
    @53
    @58
    @2
    c1
    @57
    cif
    @55
    @53
    @2
    @56
    c1
    @57
    @53
    @2
    wa
    @3
    @53
    @24
    @2
    @54
    adantr
    @53
    @28
    @2
    @53
    @1
    cB
    cD
    cU
    cG
    cN
    cX
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrmhm.b
    dchrn0.b
    dchrn0.u
    wph
    @20
    @23
    dchrmulid2.x
    adantr
    wph
    @23
    simpr
    dchrn0
    biimpar
    recid2d
    ifeq1da
    @53
    @2
    @57
    cc0
    c1
    @53
    @3
    @54
    mul02d
    ifeq2d
    eqtrd
    syl5eq
    mpteq2dva
    dchr1cl.o
    syl6reqr
    eqtr4d
    eqtrd
    jca
end
