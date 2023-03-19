include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "cmpt.mm"
include "cdv.mm"
include "reccld.mm"
include "dvmptcmul.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "adantr.mm"
include "cc0.mm"
include "wne.mm"
include "divrec2d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "dvmptcl.mm"
include "3eqtr4d.mm"

theorem dvmptdivc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cV: class V
  let cX: class X
  let cW: class W
  let cY: class Y
  let cZ: class Z
  assume dvmptadd.s: |- ( ph -> S e. { RR , CC } )
  assume dvmptadd.a: |- ( ( ph /\ x e. X ) -> A e. CC )
  assume dvmptadd.b: |- ( ( ph /\ x e. X ) -> B e. V )
  assume dvmptadd.da: |- ( ph -> ( S _D ( x e. X |-> A ) ) = ( x e. X |-> B ) )
  assume dvmptcmul.c: |- ( ph -> C e. CC )
  assume dvmptdivc.0: |- ( ph -> C =/= 0 )

  disjoint C x
  disjoint ph x
  disjoint S x
  disjoint V x
  disjoint X x
  disjoint W x
  disjoint Y x
  disjoint Z x
  assert |- ( ph -> ( S _D ( x e. X |-> ( A / C ) ) ) = ( x e. X |-> ( B / C ) ) )

  proof
    wph
    cS
    vx
    cX
    c1
    cC
    cdiv
    co
    #
    cA
    cmul
    co
    #
    cmpt
    #
    cdv
    co
    vx
    cX
    @0
    cB
    cmul
    co
    #
    cmpt
    cS
    vx
    cX
    cA
    cC
    cdiv
    co
    #
    cmpt
    #
    cdv
    co
    vx
    cX
    cB
    cC
    cdiv
    co
    #
    cmpt
    wph
    vx
    cA
    cB
    @0
    cS
    cV
    cX
    dvmptadd.s
    dvmptadd.a
    dvmptadd.b
    dvmptadd.da
    wph
    cC
    dvmptcmul.c
    dvmptdivc.0
    reccld
    dvmptcmul
    wph
    @5
    @2
    cS
    cdv
    wph
    vx
    cX
    @4
    @1
    wph
    vx
    cv
    cX
    wcel
    #
    wa
    #
    cA
    cC
    dvmptadd.a
    wph
    cC
    cc
    wcel
    @7
    dvmptcmul.c
    adantr
    #
    wph
    cC
    cc0
    wne
    @7
    dvmptdivc.0
    adantr
    #
    divrec2d
    mpteq2dva
    oveq2d
    wph
    vx
    cX
    @6
    @3
    @8
    cB
    cC
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
    @9
    @10
    divrec2d
    mpteq2dva
    3eqtr4d
end
