include "cmpt.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cdv.mm"
include "caddc.mm"
include "cc.mm"
include "eqid.mm"
include "fmptd.mm"
include "cdm.mm"
include "dmeqd.mm"
include "wcel.mm"
include "wral.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "syl.mm"
include "eqtrd.mm"
include "dvmulf.mm"
include "cvv.mm"
include "ovex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "eqidd.mm"
include "offval2.mm"
include "oveq2d.mm"
include "cv.mm"
include "wa.mm"
include "ovexd.mm"
include "3eqtr3d.mm"

theorem dvmptmul
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
  assume dvmptadd.c: |- ( ( ph /\ x e. X ) -> C e. CC )
  assume dvmptadd.d: |- ( ( ph /\ x e. X ) -> D e. W )
  assume dvmptadd.dc: |- ( ph -> ( S _D ( x e. X |-> C ) ) = ( x e. X |-> D ) )

  disjoint ph x
  disjoint S x
  disjoint V x
  disjoint W x
  disjoint X x
  disjoint Y x
  disjoint Z x
  assert |- ( ph -> ( S _D ( x e. X |-> ( A x. C ) ) ) = ( x e. X |-> ( ( B x. C ) + ( D x. A ) ) ) )

  proof
    wph
    cS
    vx
    cX
    cA
    cmpt
    #
    vx
    cX
    cC
    cmpt
    #
    cmul
    cof
    #
    co
    #
    cdv
    co
    cS
    @0
    cdv
    co
    #
    @1
    @2
    co
    #
    cS
    @1
    cdv
    co
    #
    @0
    @2
    co
    #
    caddc
    cof
    co
    cS
    vx
    cX
    cA
    cC
    cmul
    co
    cmpt
    #
    cdv
    co
    vx
    cX
    cB
    cC
    cmul
    co
    #
    cD
    cA
    cmul
    co
    #
    caddc
    co
    cmpt
    wph
    cS
    @0
    @1
    cX
    dvmptadd.s
    wph
    vx
    cX
    cA
    cc
    @0
    dvmptadd.a
    @0
    eqid
    fmptd
    wph
    vx
    cX
    cC
    cc
    @1
    dvmptadd.c
    @1
    eqid
    fmptd
    wph
    @4
    cdm
    vx
    cX
    cB
    cmpt
    #
    cdm
    #
    cX
    wph
    @4
    @11
    dvmptadd.da
    dmeqd
    wph
    cB
    cV
    wcel
    #
    vx
    cX
    wral
    @12
    cX
    wceq
    wph
    @13
    vx
    cX
    dvmptadd.b
    ralrimiva
    vx
    cX
    cB
    cV
    dmmptg
    syl
    eqtrd
    wph
    @6
    cdm
    #
    vx
    cX
    cD
    cmpt
    #
    cdm
    #
    cX
    wph
    @6
    @15
    dvmptadd.dc
    dmeqd
    wph
    cD
    cW
    wcel
    #
    vx
    cX
    wral
    @16
    cX
    wceq
    wph
    @17
    vx
    cX
    dvmptadd.d
    ralrimiva
    vx
    cX
    cD
    cW
    dmmptg
    syl
    eqtrd
    #
    dvmulf
    wph
    @3
    @8
    cS
    cdv
    wph
    vx
    cX
    cA
    cC
    cmul
    @0
    @1
    cvv
    cc
    cc
    wph
    cX
    @14
    cvv
    @18
    @6
    cS
    @1
    cdv
    ovex
    dmex
    syl6eqelr
    #
    dvmptadd.a
    dvmptadd.c
    wph
    @0
    eqidd
    #
    wph
    @1
    eqidd
    #
    offval2
    oveq2d
    wph
    vx
    cX
    @9
    @10
    caddc
    @5
    @7
    cvv
    cvv
    cvv
    @19
    wph
    vx
    cv
    cX
    wcel
    wa
    #
    cB
    cC
    cmul
    ovexd
    @22
    cD
    cA
    cmul
    ovexd
    wph
    vx
    cX
    cB
    cC
    cmul
    @4
    @1
    cvv
    cV
    cc
    @19
    dvmptadd.b
    dvmptadd.c
    dvmptadd.da
    @21
    offval2
    wph
    vx
    cX
    cD
    cA
    cmul
    @6
    @0
    cvv
    cW
    cc
    @19
    dvmptadd.d
    dvmptadd.a
    dvmptadd.dc
    @20
    offval2
    offval2
    3eqtr3d
end
