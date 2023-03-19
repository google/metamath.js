include "c1.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "cdv.mm"
include "cc.mm"
include "wcel.mm"
include "neg1cn.mm"
include "a1i.mm"
include "dvmptcmul.mm"
include "cv.mm"
include "wa.mm"
include "mulm1d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "dvmptcl.mm"
include "3eqtr3d.mm"

theorem dvmptneg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
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

  disjoint ph x
  disjoint S x
  disjoint V x
  disjoint X x
  disjoint W x
  disjoint Y x
  disjoint Z x
  assert |- ( ph -> ( S _D ( x e. X |-> -u A ) ) = ( x e. X |-> -u B ) )

  proof
    wph
    cS
    vx
    cX
    c1
    cneg
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
    cneg
    #
    cmpt
    #
    cdv
    co
    vx
    cX
    cB
    cneg
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
    @0
    cc
    wcel
    wph
    neg1cn
    a1i
    dvmptcmul
    wph
    @2
    @5
    cS
    cdv
    wph
    vx
    cX
    @1
    @4
    wph
    vx
    cv
    cX
    wcel
    wa
    #
    cA
    dvmptadd.a
    mulm1d
    mpteq2dva
    oveq2d
    wph
    vx
    cX
    @3
    @6
    @7
    cB
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
    mulm1d
    mpteq2dva
    3eqtr3d
end
