include "cdvr.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "csu.mm"
include "cur.mm"
include "wceq.mm"
include "cphi.mm"
include "cc0.mm"
include "cif.mm"
include "ccj.mm"
include "cmul.mm"
include "eqid.mm"
include "crg.mm"
include "wcel.mm"
include "cn0.mm"
include "ccrg.mm"
include "nnnn0d.mm"
include "zncrng.mm"
include "crngring.mm"
include "3syl.mm"
include "dvrcl.mm"
include "syl3anc.mm"
include "sumdchr.mm"
include "wa.mm"
include "cinvr.mm"
include "cmulr.mm"
include "dvrval.mm"
include "syl2anc.mm"
include "adantr.mm"
include "fveq2d.mm"
include "cmgp.mm"
include "ccnfld.mm"
include "cmhm.mm"
include "dchrmhm.mm"
include "simpr.mm"
include "sseldi.mm"
include "unitss.mm"
include "unitinvcl.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "cnfldmul.mm"
include "mhmlin.mm"
include "cres.mm"
include "cress.mm"
include "cc.mm"
include "csn.mm"
include "cdif.mm"
include "cghm.mm"
include "dchrghm.mm"
include "unitgrpbas.mm"
include "invrfval.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cndrng.mm"
include "drngui.mm"
include "ghminv.mm"
include "fvres.mm"
include "syl.mm"
include "c1.mm"
include "cdiv.mm"
include "wne.mm"
include "dchrf.mm"
include "ffvelrnd.mm"
include "dchrn0.mm"
include "mpbird.mm"
include "cnfldinv.mm"
include "cabs.mm"
include "c2.mm"
include "cexp.mm"
include "recval.mm"
include "dchrabs.mm"
include "oveq1d.mm"
include "sq1.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "cjcld.mm"
include "div1d.mm"
include "3eqtrd.mm"
include "3eqtr3d.mm"
include "sumeq2dv.mm"
include "wb.mm"
include "dvreq1.mm"
include "ifbid.mm"

theorem sum2dchr
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let cG: class G
  let cN: class N
  let cZ: class Z
  assume sum2dchr.g: |- G = ( DChr ` N )
  assume sum2dchr.d: |- D = ( Base ` G )
  assume sum2dchr.z: |- Z = ( Z/nZ ` N )
  assume sum2dchr.b: |- B = ( Base ` Z )
  assume sum2dchr.u: |- U = ( Unit ` Z )
  assume sum2dchr.n: |- ( ph -> N e. NN )
  assume sum2dchr.a: |- ( ph -> A e. B )
  assume sum2dchr.c: |- ( ph -> C e. U )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint G x
  disjoint N x
  disjoint ph x
  disjoint Z x
  assert |- ( ph -> sum_ x e. D ( ( x ` A ) x. ( * ` ( x ` C ) ) ) = if ( A = C , ( phi ` N ) , 0 ) )

  proof
    wph
    cD
    cA
    cC
    cZ
    cdvr
    cfv
    #
    co
    #
    vx
    cv
    #
    cfv
    #
    vx
    csu
    @1
    cZ
    cur
    cfv
    #
    wceq
    #
    cN
    cphi
    cfv
    #
    cc0
    cif
    cD
    cA
    @2
    cfv
    #
    cC
    @2
    cfv
    #
    ccj
    cfv
    #
    cmul
    co
    #
    vx
    csu
    cA
    cC
    wceq
    #
    @6
    cc0
    cif
    wph
    vx
    @1
    cB
    cD
    @4
    cG
    cN
    cZ
    sum2dchr.g
    sum2dchr.d
    sum2dchr.z
    @4
    eqid
    #
    sum2dchr.b
    sum2dchr.n
    wph
    cZ
    crg
    wcel
    #
    cA
    cB
    wcel
    #
    cC
    cU
    wcel
    #
    @1
    cB
    wcel
    wph
    cN
    cn0
    wcel
    cZ
    ccrg
    wcel
    @13
    wph
    cN
    sum2dchr.n
    nnnn0d
    cN
    cZ
    sum2dchr.z
    zncrng
    cZ
    crngring
    3syl
    #
    sum2dchr.a
    sum2dchr.c
    cB
    @0
    cZ
    cU
    cA
    cC
    sum2dchr.b
    sum2dchr.u
    @0
    eqid
    #
    dvrcl
    syl3anc
    sumdchr
    wph
    cD
    @3
    @10
    vx
    wph
    @2
    cD
    wcel
    #
    wa
    #
    @3
    cA
    cC
    cZ
    cinvr
    cfv
    #
    cfv
    #
    cZ
    cmulr
    cfv
    #
    co
    #
    @2
    cfv
    #
    @7
    @21
    @2
    cfv
    #
    cmul
    co
    #
    @10
    @19
    @1
    @23
    @2
    wph
    @1
    @23
    wceq
    #
    @18
    wph
    @14
    @15
    @27
    sum2dchr.a
    sum2dchr.c
    cB
    @0
    cZ
    @22
    cU
    @20
    cA
    cC
    sum2dchr.b
    @22
    eqid
    #
    sum2dchr.u
    @20
    eqid
    #
    @17
    dvrval
    syl2anc
    adantr
    fveq2d
    @19
    @2
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
    @14
    @21
    cB
    wcel
    @24
    @26
    wceq
    @19
    cD
    @32
    @2
    cD
    cG
    cN
    cZ
    sum2dchr.g
    sum2dchr.z
    sum2dchr.d
    dchrmhm
    wph
    @18
    simpr
    #
    sseldi
    wph
    @14
    @18
    sum2dchr.a
    adantr
    @19
    cU
    cB
    @21
    cB
    cZ
    cU
    sum2dchr.b
    sum2dchr.u
    unitss
    #
    wph
    @21
    cU
    wcel
    #
    @18
    wph
    @13
    @15
    @35
    @16
    sum2dchr.c
    cZ
    cU
    @20
    cC
    sum2dchr.u
    @29
    unitinvcl
    syl2anc
    adantr
    #
    sseldi
    cB
    @22
    cmul
    @30
    @31
    @2
    cA
    @21
    cB
    cZ
    @30
    @30
    eqid
    #
    sum2dchr.b
    mgpbas
    cZ
    @22
    @30
    @37
    @28
    mgpplusg
    ccnfld
    cmul
    @31
    @31
    eqid
    cnfldmul
    mgpplusg
    mhmlin
    syl3anc
    @19
    @25
    @9
    @7
    cmul
    @19
    @21
    @2
    cU
    cres
    #
    cfv
    #
    cC
    @38
    cfv
    #
    ccnfld
    cinvr
    cfv
    #
    cfv
    #
    @25
    @9
    @19
    @38
    @30
    cU
    cress
    co
    #
    @31
    cc
    cc0
    csn
    cdif
    #
    cress
    co
    #
    cghm
    co
    wcel
    @15
    @39
    @42
    wceq
    @19
    cD
    cU
    cG
    @43
    @45
    cN
    @2
    cZ
    sum2dchr.g
    sum2dchr.z
    sum2dchr.d
    sum2dchr.u
    @43
    eqid
    #
    @45
    eqid
    #
    @33
    dchrghm
    wph
    @15
    @18
    sum2dchr.c
    adantr
    #
    cU
    @43
    @45
    @38
    @20
    @41
    cC
    cZ
    cU
    @43
    sum2dchr.u
    @46
    unitgrpbas
    cZ
    cU
    @43
    @20
    sum2dchr.u
    @46
    @29
    invrfval
    ccnfld
    @44
    @45
    @41
    cc
    ccnfld
    cc0
    cnfldbas
    cnfld0
    cndrng
    drngui
    @47
    @41
    eqid
    invrfval
    ghminv
    syl2anc
    @19
    @35
    @39
    @25
    wceq
    @36
    @21
    cU
    @2
    fvres
    syl
    @19
    @42
    @8
    @41
    cfv
    #
    c1
    @8
    cdiv
    co
    #
    @9
    @19
    @40
    @8
    @41
    @19
    @15
    @40
    @8
    wceq
    @48
    cC
    cU
    @2
    fvres
    syl
    fveq2d
    @19
    @8
    cc
    wcel
    #
    @8
    cc0
    wne
    #
    @49
    @50
    wceq
    @19
    cB
    cc
    cC
    @2
    @19
    cB
    cD
    cG
    cN
    @2
    cZ
    sum2dchr.g
    sum2dchr.z
    sum2dchr.d
    sum2dchr.b
    @33
    dchrf
    @19
    cU
    cB
    cC
    @34
    @48
    sseldi
    #
    ffvelrnd
    #
    @19
    @52
    @15
    @48
    @19
    cC
    cB
    cD
    cU
    cG
    cN
    @2
    cZ
    sum2dchr.g
    sum2dchr.z
    sum2dchr.d
    sum2dchr.b
    sum2dchr.u
    @33
    @53
    dchrn0
    mpbird
    #
    @8
    cnfldinv
    syl2anc
    @19
    @50
    @9
    @8
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @9
    c1
    cdiv
    co
    @9
    @19
    @51
    @52
    @50
    @58
    wceq
    @54
    @55
    @8
    recval
    syl2anc
    @19
    @57
    c1
    @9
    cdiv
    @19
    @57
    c1
    c2
    cexp
    co
    c1
    @19
    @56
    c1
    c2
    cexp
    @19
    cC
    cD
    cU
    cG
    cN
    @2
    cZ
    sum2dchr.g
    sum2dchr.d
    @33
    sum2dchr.z
    sum2dchr.u
    @48
    dchrabs
    oveq1d
    sq1
    syl6eq
    oveq2d
    @19
    @9
    @19
    @8
    @54
    cjcld
    div1d
    3eqtrd
    3eqtrd
    3eqtr3d
    oveq2d
    3eqtrd
    sumeq2dv
    wph
    @5
    @11
    @6
    cc0
    wph
    @13
    @14
    @15
    @5
    @11
    wb
    @16
    sum2dchr.a
    sum2dchr.c
    cB
    @0
    cZ
    cU
    @4
    cA
    cC
    sum2dchr.b
    sum2dchr.u
    @17
    @12
    dvreq1
    syl3anc
    ifbid
    3eqtr3d
end
