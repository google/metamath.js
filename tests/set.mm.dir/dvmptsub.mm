include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "cdv.mm"
include "cmin.mm"
include "cvv.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "negcld.mm"
include "negex.mm"
include "a1i.mm"
include "dvmptneg.mm"
include "dvmptadd.mm"
include "negsubd.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "dvmptcl.mm"
include "3eqtr3d.mm"

theorem dvmptsub
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume dvmptadd.s: |- ( ph -> S e. { RR , CC } )
  assume dvmptadd.a: |- ( ( ph /\ x e. X ) -> A e. CC )
  assume dvmptadd.b: |- ( ( ph /\ x e. X ) -> B e. V )
  assume dvmptadd.da: |- ( ph -> ( S _D ( x e. X |-> A ) ) = ( x e. X |-> B ) )
  assume dvmptsub.c: |- ( ( ph /\ x e. X ) -> C e. CC )
  assume dvmptsub.d: |- ( ( ph /\ x e. X ) -> D e. W )
  assume dvmptsub.dc: |- ( ph -> ( S _D ( x e. X |-> C ) ) = ( x e. X |-> D ) )

  disjoint ph x
  disjoint S x
  disjoint V x
  disjoint W x
  disjoint X x
  disjoint Y x
  disjoint Z x
  assert |- ( ph -> ( S _D ( x e. X |-> ( A - C ) ) ) = ( x e. X |-> ( B - D ) ) )

  proof
    wph
    cS
    vx
    cX
    cA
    cC
    cneg
    #
    caddc
    co
    #
    cmpt
    #
    cdv
    co
    vx
    cX
    cB
    cD
    cneg
    #
    caddc
    co
    #
    cmpt
    cS
    vx
    cX
    cA
    cC
    cmin
    co
    #
    cmpt
    #
    cdv
    co
    vx
    cX
    cB
    cD
    cmin
    co
    #
    cmpt
    wph
    vx
    cA
    cB
    @0
    @3
    cS
    cV
    cvv
    cX
    dvmptadd.s
    dvmptadd.a
    dvmptadd.b
    dvmptadd.da
    wph
    vx
    cv
    cX
    wcel
    wa
    #
    cC
    dvmptsub.c
    negcld
    @3
    cvv
    wcel
    @8
    cD
    negex
    a1i
    wph
    vx
    cC
    cD
    cS
    cW
    cX
    dvmptadd.s
    dvmptsub.c
    dvmptsub.d
    dvmptsub.dc
    dvmptneg
    dvmptadd
    wph
    @2
    @6
    cS
    cdv
    wph
    vx
    cX
    @1
    @5
    @8
    cA
    cC
    dvmptadd.a
    dvmptsub.c
    negsubd
    mpteq2dva
    oveq2d
    wph
    vx
    cX
    @4
    @7
    @8
    cB
    cD
    wph
    vx
    cA
    cB
    cS
    cV
    cX
    dvmptadd.s
    dvmptadd.a
    dvmptadd.b
    dvmptadd.da
    dvmptcl
    wph
    vx
    cC
    cD
    cS
    cW
    cX
    dvmptadd.s
    dvmptsub.c
    dvmptsub.d
    dvmptsub.dc
    dvmptcl
    negsubd
    mpteq2dva
    3eqtr3d
end
