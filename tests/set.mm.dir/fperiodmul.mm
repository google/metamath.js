include "cn0.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cr.mm"
include "cc.mm"
include "wf.mm"
include "adantr.mm"
include "simpr.mm"
include "cv.mm"
include "adantlr.mm"
include "fperiodmullem.mm"
include "wn.mm"
include "cneg.mm"
include "cmin.mm"
include "recnd.mm"
include "zcnd.mm"
include "mulcld.mm"
include "subnegd.mm"
include "mulneg1d.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "cz.mm"
include "cn.mm"
include "znnn0nn.mm"
include "sylan.mm"
include "nnnn0d.mm"
include "zred.mm"
include "renegcld.mm"
include "remulcld.mm"
include "resubcld.mm"
include "negcld.mm"
include "npcand.mm"
include "3eqtr2d.mm"
include "pm2.61dan.mm"

theorem fperiodmul
  let wph: wff ph
  let vx: setvar x
  let cT: class T
  let cF: class F
  let cN: class N
  let cX: class X
  assume fperiodmul.f: |- ( ph -> F : RR --> CC )
  assume fperiodmul.t: |- ( ph -> T e. RR )
  assume fperiodmul.n: |- ( ph -> N e. ZZ )
  assume fperiodmul.x: |- ( ph -> X e. RR )
  assume fperiodmul.per: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )

  disjoint F x
  disjoint N x
  disjoint T x
  disjoint X x
  disjoint ph x
  assert |- ( ph -> ( F ` ( X + ( N x. T ) ) ) = ( F ` X ) )

  proof
    wph
    cN
    cn0
    wcel
    #
    cX
    cN
    cT
    cmul
    co
    #
    caddc
    co
    #
    cF
    cfv
    #
    cX
    cF
    cfv
    #
    wceq
    wph
    @0
    wa
    vx
    cT
    cF
    cN
    cX
    wph
    cr
    cc
    cF
    wf
    #
    @0
    fperiodmul.f
    adantr
    wph
    cT
    cr
    wcel
    #
    @0
    fperiodmul.t
    adantr
    wph
    @0
    simpr
    wph
    cX
    cr
    wcel
    #
    @0
    fperiodmul.x
    adantr
    wph
    vx
    cv
    #
    cr
    wcel
    #
    @8
    cT
    caddc
    co
    cF
    cfv
    @8
    cF
    cfv
    wceq
    #
    @0
    fperiodmul.per
    adantlr
    fperiodmullem
    wph
    @0
    wn
    #
    wa
    #
    @3
    cX
    cN
    cneg
    #
    cT
    cmul
    co
    #
    cmin
    co
    #
    cF
    cfv
    #
    @15
    @14
    caddc
    co
    #
    cF
    cfv
    @4
    wph
    @3
    @16
    wceq
    @11
    wph
    @2
    @15
    cF
    wph
    cX
    @1
    cneg
    #
    cmin
    co
    @2
    @15
    wph
    cX
    @1
    wph
    cX
    fperiodmul.x
    recnd
    wph
    cN
    cT
    wph
    cN
    fperiodmul.n
    zcnd
    #
    wph
    cT
    fperiodmul.t
    recnd
    #
    mulcld
    subnegd
    wph
    @18
    @14
    cX
    cmin
    wph
    @14
    @18
    wph
    cN
    cT
    @19
    @20
    mulneg1d
    eqcomd
    oveq2d
    eqtr3d
    fveq2d
    adantr
    @12
    vx
    cT
    cF
    @13
    @15
    wph
    @5
    @11
    fperiodmul.f
    adantr
    wph
    @6
    @11
    fperiodmul.t
    adantr
    #
    @12
    @13
    wph
    cN
    cz
    wcel
    #
    @11
    @13
    cn
    wcel
    fperiodmul.n
    cN
    znnn0nn
    sylan
    nnnn0d
    @12
    cX
    @14
    wph
    @7
    @11
    fperiodmul.x
    adantr
    #
    @12
    @13
    cT
    @12
    cN
    @12
    cN
    wph
    @22
    @11
    fperiodmul.n
    adantr
    zred
    #
    renegcld
    @21
    remulcld
    resubcld
    wph
    @9
    @10
    @11
    fperiodmul.per
    adantlr
    fperiodmullem
    @12
    @17
    cX
    cF
    @12
    cX
    @14
    @12
    cX
    @23
    recnd
    @12
    @13
    cT
    @12
    cN
    @12
    cN
    @24
    recnd
    negcld
    @12
    cT
    @21
    recnd
    mulcld
    npcand
    fveq2d
    3eqtr2d
    pm2.61dan
end
