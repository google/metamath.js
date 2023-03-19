include "cmpt.mm"
include "ccom.mm"
include "cdv.mm"
include "co.mm"
include "cmul.mm"
include "cof.mm"
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
include "dvcof.mm"
include "eqidd.mm"
include "fmptco.mm"
include "oveq2d.mm"
include "cvv.mm"
include "ovex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "wf.mm"
include "dvmptcl.mm"
include "feq1d.mm"
include "mpbird.mm"
include "fco.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "offval2.mm"
include "3eqtr3d.mm"

theorem dvmptco
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cE: class E
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dvmptco.s: |- ( ph -> S e. { RR , CC } )
  assume dvmptco.t: |- ( ph -> T e. { RR , CC } )
  assume dvmptco.a: |- ( ( ph /\ x e. X ) -> A e. Y )
  assume dvmptco.b: |- ( ( ph /\ x e. X ) -> B e. V )
  assume dvmptco.c: |- ( ( ph /\ y e. Y ) -> C e. CC )
  assume dvmptco.d: |- ( ( ph /\ y e. Y ) -> D e. W )
  assume dvmptco.da: |- ( ph -> ( S _D ( x e. X |-> A ) ) = ( x e. X |-> B ) )
  assume dvmptco.dc: |- ( ph -> ( T _D ( y e. Y |-> C ) ) = ( y e. Y |-> D ) )
  assume dvmptco.e: |- ( y = A -> C = E )
  assume dvmptco.f: |- ( y = A -> D = F )

  disjoint A y
  disjoint C x
  disjoint D x
  disjoint E y
  disjoint F y
  disjoint T y
  disjoint V x
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint W y
  disjoint X x
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( S _D ( x e. X |-> E ) ) = ( x e. X |-> ( F x. B ) ) )

  proof
    wph
    cS
    vy
    cY
    cC
    cmpt
    #
    vx
    cX
    cA
    cmpt
    #
    ccom
    #
    cdv
    co
    cT
    @0
    cdv
    co
    #
    @1
    ccom
    #
    cS
    @1
    cdv
    co
    #
    cmul
    cof
    co
    cS
    vx
    cX
    cE
    cmpt
    #
    cdv
    co
    vx
    cX
    cF
    cB
    cmul
    co
    cmpt
    wph
    cT
    cS
    @0
    @1
    cY
    cX
    dvmptco.t
    dvmptco.s
    wph
    vy
    cY
    cC
    cc
    @0
    dvmptco.c
    @0
    eqid
    fmptd
    wph
    vx
    cX
    cA
    cY
    @1
    dvmptco.a
    @1
    eqid
    fmptd
    #
    wph
    @3
    cdm
    vy
    cY
    cD
    cmpt
    #
    cdm
    #
    cY
    wph
    @3
    @8
    dvmptco.dc
    dmeqd
    wph
    cD
    cW
    wcel
    #
    vy
    cY
    wral
    @9
    cY
    wceq
    wph
    @10
    vy
    cY
    dvmptco.d
    ralrimiva
    vy
    cY
    cD
    cW
    dmmptg
    syl
    eqtrd
    wph
    @5
    cdm
    #
    vx
    cX
    cB
    cmpt
    #
    cdm
    #
    cX
    wph
    @5
    @12
    dvmptco.da
    dmeqd
    wph
    cB
    cV
    wcel
    #
    vx
    cX
    wral
    @13
    cX
    wceq
    wph
    @14
    vx
    cX
    dvmptco.b
    ralrimiva
    vx
    cX
    cB
    cV
    dmmptg
    syl
    eqtrd
    #
    dvcof
    wph
    @2
    @6
    cS
    cdv
    wph
    vx
    vy
    cX
    cY
    cA
    cC
    cE
    @1
    @0
    dvmptco.a
    wph
    @1
    eqidd
    #
    wph
    @0
    eqidd
    dvmptco.e
    fmptco
    oveq2d
    wph
    vx
    cX
    cF
    cB
    cmul
    @4
    @5
    cvv
    cc
    cV
    wph
    cX
    @11
    cvv
    @15
    @5
    cS
    @1
    cdv
    ovex
    dmex
    syl6eqelr
    wph
    cF
    cc
    wcel
    #
    vx
    cX
    wph
    cX
    cc
    vx
    cX
    cF
    cmpt
    #
    wf
    #
    @17
    vx
    cX
    wral
    wph
    cX
    cc
    @4
    wf
    #
    @19
    wph
    cY
    cc
    @3
    wf
    #
    cX
    cY
    @1
    wf
    @20
    wph
    @21
    cY
    cc
    @8
    wf
    wph
    vy
    cY
    cD
    cc
    @8
    wph
    vy
    cC
    cD
    cT
    cW
    cY
    dvmptco.t
    dvmptco.c
    dvmptco.d
    dvmptco.dc
    dvmptcl
    @8
    eqid
    fmptd
    wph
    cY
    cc
    @3
    @8
    dvmptco.dc
    feq1d
    mpbird
    @7
    cX
    cY
    cc
    @3
    @1
    fco
    syl2anc
    wph
    cX
    cc
    @4
    @18
    wph
    vx
    vy
    cX
    cY
    cA
    cD
    cF
    @1
    @3
    dvmptco.a
    @16
    dvmptco.dc
    dvmptco.f
    fmptco
    #
    feq1d
    mpbid
    vx
    cX
    cc
    cF
    @18
    @18
    eqid
    fmpt
    sylibr
    r19.21bi
    dvmptco.b
    @22
    dvmptco.da
    offval2
    3eqtr3d
end
