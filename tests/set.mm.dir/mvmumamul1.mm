include "cv.mm"
include "cfv.mm"
include "c0.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wcel.mm"
include "cmulr.mm"
include "cmpt.mm"
include "cgsu.mm"
include "crg.mm"
include "eqid.mm"
include "adantr.mm"
include "cfn.mm"
include "cxp.mm"
include "cmap.mm"
include "simpr.mm"
include "mvmulfv.mm"
include "adantlr.mm"
include "wi.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "rspccv.mm"
include "adantl.mm"
include "imp.mm"
include "oveq2d.mm"
include "mpteq2dva.mm"
include "csn.mm"
include "snfi.mm"
include "a1i.mm"
include "0ex.mm"
include "snid.mm"
include "mamufv.mm"
include "eqcomd.mm"
include "3eqtrd.mm"
include "ralrimiva.mm"
include "ex.mm"

theorem mvmumamul1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let vi: setvar i
  let vj: setvar j
  let cM: class M
  let cN: class N
  let cY: class Y
  let cZ: class Z
  let vk: setvar k
  assume mvmumamul1.x: |- .X. = ( R maMul <. M , N , { (/) } >. )
  assume mvmumamul1.t: |- .x. = ( R maVecMul <. M , N >. )
  assume mvmumamul1.b: |- B = ( Base ` R )
  assume mvmumamul1.r: |- ( ph -> R e. Ring )
  assume mvmumamul1.m: |- ( ph -> M e. Fin )
  assume mvmumamul1.n: |- ( ph -> N e. Fin )
  assume mvmumamul1.a: |- ( ph -> A e. ( B ^m ( M X. N ) ) )
  assume mvmumamul1.y: |- ( ph -> Y e. ( B ^m N ) )
  assume mvmumamul1.z: |- ( ph -> Z e. ( B ^m ( N X. { (/) } ) ) )

  disjoint i j
  disjoint N i
  disjoint N j
  disjoint Y i
  disjoint Y j
  disjoint Z i
  disjoint Z j
  disjoint i ph
  disjoint j ph
  disjoint A k
  disjoint M k
  disjoint i k
  disjoint j k
  disjoint N k
  disjoint R k
  disjoint Y k
  disjoint Z k
  disjoint k ph
  assert |- ( ph -> ( A. j e. N ( Y ` j ) = ( j Z (/) ) -> A. i e. M ( ( A .x. Y ) ` i ) = ( i ( A .X. Z ) (/) ) ) )

  proof
    wph
    vj
    cv
    #
    cY
    cfv
    #
    @0
    c0
    cZ
    co
    #
    wceq
    #
    vj
    cN
    wral
    #
    vi
    cv
    #
    cA
    cY
    c.x
    co
    cfv
    #
    @5
    c0
    cA
    cZ
    c.xp
    co
    co
    #
    wceq
    #
    vi
    cM
    wral
    wph
    @4
    wa
    #
    @8
    vi
    cM
    @9
    @5
    cM
    wcel
    #
    wa
    @6
    cR
    vk
    cN
    @5
    vk
    cv
    #
    cA
    co
    #
    @11
    cY
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cR
    vk
    cN
    @12
    @11
    c0
    cZ
    co
    #
    @14
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @7
    wph
    @10
    @6
    @17
    wceq
    @4
    wph
    @10
    wa
    #
    cB
    cR
    @14
    c.x
    vk
    @5
    cM
    cN
    crg
    cA
    cY
    mvmumamul1.t
    mvmumamul1.b
    @14
    eqid
    #
    wph
    cR
    crg
    wcel
    @10
    mvmumamul1.r
    adantr
    #
    wph
    cM
    cfn
    wcel
    @10
    mvmumamul1.m
    adantr
    #
    wph
    cN
    cfn
    wcel
    @10
    mvmumamul1.n
    adantr
    #
    wph
    cA
    cB
    cM
    cN
    cxp
    cmap
    co
    wcel
    @10
    mvmumamul1.a
    adantr
    #
    wph
    cY
    cB
    cN
    cmap
    co
    wcel
    @10
    mvmumamul1.y
    adantr
    wph
    @10
    simpr
    #
    mvmulfv
    adantlr
    @9
    @17
    @21
    wceq
    @10
    @9
    @16
    @20
    cR
    cgsu
    @9
    vk
    cN
    @15
    @19
    @9
    @11
    cN
    wcel
    #
    wa
    @13
    @18
    @12
    @14
    @9
    @29
    @13
    @18
    wceq
    #
    @4
    @29
    @30
    wi
    wph
    @3
    @30
    vj
    @11
    cN
    vj
    vk
    weq
    @1
    @13
    @2
    @18
    @0
    @11
    cY
    fveq2
    @0
    @11
    c0
    cZ
    oveq1
    eqeq12d
    rspccv
    adantl
    imp
    oveq2d
    mpteq2dva
    oveq2d
    adantr
    wph
    @10
    @21
    @7
    wceq
    @4
    @22
    @7
    @21
    @22
    cB
    c0
    csn
    #
    cR
    @14
    vk
    c.xp
    @5
    c0
    cM
    cN
    crg
    cA
    cZ
    mvmumamul1.x
    mvmumamul1.b
    @23
    @24
    @25
    @26
    @31
    cfn
    wcel
    @22
    c0
    snfi
    a1i
    @27
    wph
    cZ
    cB
    cN
    @31
    cxp
    cmap
    co
    wcel
    @10
    mvmumamul1.z
    adantr
    @28
    c0
    @31
    wcel
    @22
    c0
    0ex
    snid
    a1i
    mamufv
    eqcomd
    adantlr
    3eqtrd
    ralrimiva
    ex
end
