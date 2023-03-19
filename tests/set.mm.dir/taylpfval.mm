include "cc.mm"
include "cv.mm"
include "csn.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cdvn.mm"
include "cfv.mm"
include "cfa.mm"
include "cdiv.mm"
include "cmin.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cxp.mm"
include "ciun.mm"
include "cmpt.mm"
include "ccnfld.mm"
include "cicc.mm"
include "cz.mm"
include "cin.mm"
include "ctsu.mm"
include "cn0.mm"
include "wcel.mm"
include "cpnf.mm"
include "wceq.mm"
include "orcd.mm"
include "taylplem1.mm"
include "taylfval.mm"
include "wa.mm"
include "cgsu.mm"
include "ctopn.mm"
include "cvv.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "crg.mm"
include "ccmn.mm"
include "cnring.mm"
include "ringcmn.mm"
include "mp1i.mm"
include "ctps.mm"
include "cnfldtps.mm"
include "a1i.mm"
include "ovex.mm"
include "inex1.mm"
include "taylfvallem1.mm"
include "eqid.mm"
include "fmptd.mm"
include "cfn.mm"
include "0z.mm"
include "nn0zd.mm"
include "fzval2.mm"
include "sylancr.mm"
include "adantr.mm"
include "fzfid.mm"
include "eqeltrrd.mm"
include "ovexd.mm"
include "c0ex.mm"
include "fsuppmptdm.mm"
include "cha.mm"
include "cnfldhaus.mm"
include "haustsmsid.mm"
include "gsumfsum.mm"
include "sumeq1d.mm"
include "eqtr4d.mm"
include "sneqd.mm"
include "eqtrd.mm"
include "xpeq2d.mm"
include "iuneq2dv.mm"
include "dfmpt3.mm"
include "syl6eqr.mm"

theorem taylpfval
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cF: class F
  let cN: class N
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let cD: class D
  let cX: class X
  assume taylpfval.s: |- ( ph -> S e. { RR , CC } )
  assume taylpfval.f: |- ( ph -> F : A --> CC )
  assume taylpfval.a: |- ( ph -> A C_ S )
  assume taylpfval.n: |- ( ph -> N e. NN0 )
  assume taylpfval.b: |- ( ph -> B e. dom ( ( S Dn F ) ` N ) )
  assume taylpfval.t: |- T = ( N ( S Tayl F ) B )

  disjoint k x
  disjoint B k
  disjoint B x
  disjoint F k
  disjoint F x
  disjoint N k
  disjoint N x
  disjoint k ph
  disjoint ph x
  disjoint S k
  disjoint S x
  disjoint T x
  disjoint k u
  disjoint k v
  disjoint k y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint v x
  disjoint v y
  disjoint B v
  disjoint x y
  disjoint B y
  disjoint F u
  disjoint F v
  disjoint F y
  disjoint N u
  disjoint N v
  disjoint N y
  disjoint ph u
  disjoint ph v
  disjoint ph y
  disjoint D k
  disjoint D u
  disjoint D v
  disjoint D y
  disjoint S u
  disjoint S v
  disjoint S y
  disjoint X k
  disjoint X x
  assert |- ( ph -> T = ( x e. CC |-> sum_ k e. ( 0 ... N ) ( ( ( ( ( S Dn F ) ` k ) ` B ) / ( ! ` k ) ) x. ( ( x - B ) ^ k ) ) ) )

  proof
    wph
    cT
    vx
    cc
    vx
    cv
    #
    csn
    #
    cc0
    cN
    cfz
    co
    #
    cB
    vk
    cv
    #
    cS
    cF
    cdvn
    co
    cfv
    cfv
    @3
    cfa
    cfv
    cdiv
    co
    #
    @0
    cB
    cmin
    co
    @3
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    csn
    #
    cxp
    #
    ciun
    #
    vx
    cc
    @7
    cmpt
    wph
    cT
    vx
    cc
    @1
    ccnfld
    vk
    cc0
    cN
    cicc
    co
    #
    cz
    cin
    #
    @6
    cmpt
    #
    ctsu
    co
    #
    cxp
    #
    ciun
    @10
    wph
    vx
    cA
    cB
    cS
    cT
    vk
    cF
    cN
    taylpfval.s
    taylpfval.f
    taylpfval.a
    wph
    cN
    cn0
    wcel
    cN
    cpnf
    wceq
    taylpfval.n
    orcd
    #
    wph
    cA
    cB
    cS
    vk
    cF
    cN
    taylpfval.s
    taylpfval.f
    taylpfval.a
    taylpfval.n
    taylpfval.b
    taylplem1
    #
    taylpfval.t
    taylfval
    wph
    vx
    cc
    @15
    @9
    wph
    @0
    cc
    wcel
    #
    wa
    #
    @14
    @8
    @1
    @19
    @14
    ccnfld
    @13
    cgsu
    co
    #
    csn
    @8
    @19
    @12
    cc
    @13
    ccnfld
    ccnfld
    ctopn
    cfv
    #
    cvv
    cc0
    cnfldbas
    cnfld0
    ccnfld
    crg
    wcel
    ccnfld
    ccmn
    wcel
    @19
    cnring
    ccnfld
    ringcmn
    mp1i
    ccnfld
    ctps
    wcel
    @19
    cnfldtps
    a1i
    @12
    cvv
    wcel
    @19
    @11
    cz
    cc0
    cN
    cicc
    ovex
    inex1
    a1i
    @19
    vk
    @12
    @6
    cc
    @13
    wph
    cA
    cB
    cS
    vk
    cF
    cN
    @0
    taylpfval.s
    taylpfval.f
    taylpfval.a
    @16
    @17
    taylfvallem1
    #
    @13
    eqid
    #
    fmptd
    @19
    vk
    @12
    @13
    cvv
    cvv
    @6
    cc0
    @23
    @19
    @2
    @12
    cfn
    wph
    @2
    @12
    wceq
    #
    @18
    wph
    cc0
    cz
    wcel
    cN
    cz
    wcel
    @24
    0z
    wph
    cN
    taylpfval.n
    nn0zd
    cc0
    cN
    fzval2
    sylancr
    adantr
    #
    @19
    cc0
    cN
    fzfid
    eqeltrrd
    #
    @19
    @3
    @12
    wcel
    wa
    @4
    @5
    cmul
    ovexd
    cc0
    cvv
    wcel
    @19
    c0ex
    a1i
    fsuppmptdm
    @21
    eqid
    #
    @21
    cha
    wcel
    @19
    @21
    @27
    cnfldhaus
    a1i
    haustsmsid
    @19
    @20
    @7
    @19
    @20
    @12
    @6
    vk
    csu
    @7
    @19
    @12
    @6
    vk
    @26
    @22
    gsumfsum
    @19
    @2
    @12
    @6
    vk
    @25
    sumeq1d
    eqtr4d
    sneqd
    eqtrd
    xpeq2d
    iuneq2dv
    eqtrd
    vx
    cc
    @7
    dfmpt3
    syl6eqr
end
