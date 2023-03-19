include "cle.mm"
include "corvc.mm"
include "co.mm"
include "cfv.mm"
include "cdm.mm"
include "cprb.mm"
include "wcel.mm"
include "cmeas.mm"
include "domprobmeas.mm"
include "syl.mm"
include "orvclteel.mm"
include "orvclteinc.mm"
include "measssd.mm"
include "cv.mm"
include "cr.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "probvalrnd.mm"
include "fvmptd.mm"
include "3brtr4d.mm"

theorem dstfrvinc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cP: class P
  let cF: class F
  let cX: class X
  assume dstfrv.1: |- ( ph -> P e. Prob )
  assume dstfrv.2: |- ( ph -> X e. ( rRndVar ` P ) )
  assume dstfrv.3: |- ( ph -> F = ( x e. RR |-> ( P ` ( X oRVC <_ x ) ) ) )
  assume dstfrvinc.1: |- ( ph -> A e. RR )
  assume dstfrvinc.2: |- ( ph -> B e. RR )
  assume dstfrvinc.3: |- ( ph -> A <_ B )

  disjoint A x
  disjoint B x
  disjoint P x
  disjoint X x
  disjoint ph x
  assert |- ( ph -> ( F ` A ) <_ ( F ` B ) )

  proof
    wph
    cX
    cA
    cle
    corvc
    #
    co
    #
    cP
    cfv
    #
    cX
    cB
    @0
    co
    #
    cP
    cfv
    #
    cA
    cF
    cfv
    cB
    cF
    cfv
    cle
    wph
    @1
    @3
    cP
    cdm
    #
    cP
    wph
    cP
    cprb
    wcel
    cP
    @5
    cmeas
    cfv
    wcel
    dstfrv.1
    cP
    domprobmeas
    syl
    wph
    cA
    cP
    cX
    dstfrv.1
    dstfrv.2
    dstfrvinc.1
    orvclteel
    #
    wph
    cB
    cP
    cX
    dstfrv.1
    dstfrv.2
    dstfrvinc.2
    orvclteel
    #
    wph
    cA
    cB
    cP
    cX
    dstfrv.1
    dstfrv.2
    dstfrvinc.1
    dstfrvinc.2
    dstfrvinc.3
    orvclteinc
    measssd
    wph
    vx
    cA
    cX
    vx
    cv
    #
    @0
    co
    #
    cP
    cfv
    #
    @2
    cr
    cF
    cr
    dstfrv.3
    wph
    @8
    cA
    wceq
    #
    wa
    #
    @9
    @1
    cP
    @12
    @8
    cA
    cX
    @0
    wph
    @11
    simpr
    oveq2d
    fveq2d
    dstfrvinc.1
    wph
    @1
    cP
    dstfrv.1
    @6
    probvalrnd
    fvmptd
    wph
    vx
    cB
    @10
    @4
    cr
    cF
    cr
    dstfrv.3
    wph
    @8
    cB
    wceq
    #
    wa
    #
    @9
    @3
    cP
    @14
    @8
    cB
    cX
    @0
    wph
    @13
    simpr
    oveq2d
    fveq2d
    dstfrvinc.2
    wph
    @3
    cP
    dstfrv.1
    @7
    probvalrnd
    fvmptd
    3brtr4d
end
