include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wcel.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "cmgp.mm"
include "ccnfld.mm"
include "cmhm.mm"
include "co.mm"
include "wa.mm"
include "cn.mm"
include "dchrrcl.mm"
include "syl.mm"
include "dchrelbas2.mm"
include "mpbid.mm"
include "simprd.mm"
include "wceq.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "imp.mm"
include "cinvr.mm"
include "cmul.mm"
include "c1.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "cmulr.mm"
include "cur.mm"
include "crg.mm"
include "cn0.mm"
include "ccrg.mm"
include "nnnn0d.mm"
include "zncrng.mm"
include "crngring.mm"
include "3syl.mm"
include "eqid.mm"
include "unitrinv.mm"
include "sylan.mm"
include "fveq2d.mm"
include "simpld.mm"
include "adantr.mm"
include "ringinvcl.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "cnfldmul.mm"
include "mhmlin.mm"
include "syl3anc.mm"
include "ringidval.mm"
include "cnfld1.mm"
include "mhm0.mm"
include "3eqtr3d.mm"
include "cc.mm"
include "wf.mm"
include "cnfldbas.mm"
include "mhmf.mm"
include "ffvelrnd.mm"
include "mul02d.mm"
include "3netr4d.mm"
include "oveq1.mm"
include "necon3i.mm"
include "impbida.mm"

theorem dchrn0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let c.1: class .1.
  let vk: setvar k
  let cK: class K
  let cL: class L
  let cY: class Y
  assume dchrmhm.g: |- G = ( DChr ` N )
  assume dchrmhm.z: |- Z = ( Z/nZ ` N )
  assume dchrmhm.b: |- D = ( Base ` G )
  assume dchrn0.b: |- B = ( Base ` Z )
  assume dchrn0.u: |- U = ( Unit ` Z )
  assume dchrn0.x: |- ( ph -> X e. D )
  assume dchrn0.a: |- ( ph -> A e. B )


  assert |- ( ph -> ( ( X ` A ) =/= 0 <-> A e. U ) )

  proof
    wph
    cA
    cX
    cfv
    #
    cc0
    wne
    #
    cA
    cU
    wcel
    #
    wph
    @1
    @2
    wph
    cA
    cB
    wcel
    #
    vx
    cv
    #
    cX
    cfv
    #
    cc0
    wne
    #
    @4
    cU
    wcel
    #
    wi
    #
    vx
    cB
    wral
    #
    @1
    @2
    wi
    #
    dchrn0.a
    wph
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
    wcel
    #
    @9
    wph
    cX
    cD
    wcel
    #
    @13
    @9
    wa
    dchrn0.x
    wph
    vx
    cB
    cD
    cU
    cG
    cN
    cX
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrn0.b
    dchrn0.u
    wph
    @14
    cN
    cn
    wcel
    dchrn0.x
    cD
    cG
    cN
    cX
    dchrmhm.g
    dchrmhm.b
    dchrrcl
    syl
    #
    dchrmhm.b
    dchrelbas2
    mpbid
    #
    simprd
    @8
    @10
    vx
    cA
    cB
    @4
    cA
    wceq
    #
    @6
    @1
    @7
    @2
    @17
    @5
    @0
    cc0
    @4
    cA
    cX
    fveq2
    neeq1d
    @4
    cA
    cU
    eleq1
    imbi12d
    rspcv
    sylc
    imp
    wph
    @2
    wa
    #
    @0
    cA
    cZ
    cinvr
    cfv
    #
    cfv
    #
    cX
    cfv
    #
    cmul
    co
    #
    cc0
    @21
    cmul
    co
    #
    wne
    @1
    @18
    c1
    cc0
    @22
    @23
    c1
    cc0
    wne
    @18
    ax-1ne0
    a1i
    @18
    cA
    @20
    cZ
    cmulr
    cfv
    #
    co
    #
    cX
    cfv
    #
    cZ
    cur
    cfv
    #
    cX
    cfv
    #
    @22
    c1
    @18
    @25
    @27
    cX
    wph
    cZ
    crg
    wcel
    #
    @2
    @25
    @27
    wceq
    wph
    cN
    cn0
    wcel
    cZ
    ccrg
    wcel
    @29
    wph
    cN
    @15
    nnnn0d
    cN
    cZ
    dchrmhm.z
    zncrng
    cZ
    crngring
    3syl
    #
    cZ
    @24
    cU
    @27
    @19
    cA
    dchrn0.u
    @19
    eqid
    #
    @24
    eqid
    #
    @27
    eqid
    #
    unitrinv
    sylan
    fveq2d
    @18
    @13
    @3
    @20
    cB
    wcel
    #
    @26
    @22
    wceq
    wph
    @13
    @2
    wph
    @13
    @9
    @16
    simpld
    adantr
    #
    wph
    @3
    @2
    dchrn0.a
    adantr
    wph
    @29
    @2
    @34
    @30
    cB
    cZ
    cU
    @19
    cA
    dchrn0.u
    @31
    dchrn0.b
    ringinvcl
    sylan
    #
    cB
    @24
    cmul
    @11
    @12
    cX
    cA
    @20
    cB
    cZ
    @11
    @11
    eqid
    #
    dchrn0.b
    mgpbas
    #
    cZ
    @24
    @11
    @37
    @32
    mgpplusg
    ccnfld
    cmul
    @12
    @12
    eqid
    #
    cnfldmul
    mgpplusg
    mhmlin
    syl3anc
    @18
    @13
    @28
    c1
    wceq
    @35
    @11
    @12
    cX
    c1
    @27
    cZ
    @27
    @11
    @37
    @33
    ringidval
    ccnfld
    c1
    @12
    @39
    cnfld1
    ringidval
    mhm0
    syl
    3eqtr3d
    @18
    @21
    @18
    cB
    cc
    @20
    cX
    @18
    @13
    cB
    cc
    cX
    wf
    @35
    cB
    cc
    @11
    @12
    cX
    @38
    cc
    ccnfld
    @12
    @39
    cnfldbas
    mgpbas
    mhmf
    syl
    @36
    ffvelrnd
    mul02d
    3netr4d
    @0
    cc0
    @22
    @23
    @0
    cc0
    @21
    cmul
    oveq1
    necon3i
    syl
    impbida
end
