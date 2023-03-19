include "cmpt.mm"
include "caddc.mm"
include "cof.mm"
include "co.mm"
include "cdv.mm"
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
include "dvaddf.mm"
include "cvv.mm"
include "ovex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "eqidd.mm"
include "offval2.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"

theorem dvmptadd
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
  assert |- ( ph -> ( S _D ( x e. X |-> ( A + C ) ) ) = ( x e. X |-> ( B + D ) ) )

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
    caddc
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
    cS
    @1
    cdv
    co
    #
    @2
    co
    cS
    vx
    cX
    cA
    cC
    caddc
    co
    cmpt
    #
    cdv
    co
    vx
    cX
    cB
    cD
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
    @7
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
    @8
    cX
    wceq
    wph
    @9
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
    @5
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
    @5
    @11
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
    @12
    cX
    wceq
    wph
    @13
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
    dvaddf
    wph
    @3
    @6
    cS
    cdv
    wph
    vx
    cX
    cA
    cC
    caddc
    @0
    @1
    cvv
    cc
    cc
    wph
    cX
    @10
    cvv
    @14
    @5
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
    wph
    @1
    eqidd
    offval2
    oveq2d
    wph
    vx
    cX
    cB
    cD
    caddc
    @4
    @5
    cvv
    cV
    cW
    @15
    dvmptadd.b
    dvmptadd.d
    dvmptadd.da
    dvmptadd.dc
    offval2
    3eqtr3d
end
