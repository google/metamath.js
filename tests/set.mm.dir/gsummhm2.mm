include "cmpt.mm"
include "ccom.mm"
include "cgsu.mm"
include "co.mm"
include "cfv.mm"
include "eqid.mm"
include "fmptd.mm"
include "gsummhm.mm"
include "eqidd.mm"
include "fmptco.mm"
include "oveq2d.mm"
include "wcel.mm"
include "cbs.mm"
include "wceq.mm"
include "gsumcl.mm"
include "wral.mm"
include "wf.mm"
include "cmhm.mm"
include "mhmf.mm"
include "syl.mm"
include "fmpt.mm"
include "sylibr.mm"
include "cv.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"

theorem gsummhm2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cE: class E
  let cG: class G
  let cH: class H
  let cV: class V
  let cX: class X
  let c.0: class .0.
  assume gsummhm2.b: |- B = ( Base ` G )
  assume gsummhm2.z: |- .0. = ( 0g ` G )
  assume gsummhm2.g: |- ( ph -> G e. CMnd )
  assume gsummhm2.h: |- ( ph -> H e. Mnd )
  assume gsummhm2.a: |- ( ph -> A e. V )
  assume gsummhm2.k: |- ( ph -> ( x e. B |-> C ) e. ( G MndHom H ) )
  assume gsummhm2.f: |- ( ( ph /\ k e. A ) -> X e. B )
  assume gsummhm2.w: |- ( ph -> ( k e. A |-> X ) finSupp .0. )
  assume gsummhm2.1: |- ( x = X -> C = D )
  assume gsummhm2.2: |- ( x = ( G gsum ( k e. A |-> X ) ) -> C = E )

  disjoint k x
  disjoint A k
  disjoint A x
  disjoint B k
  disjoint B x
  disjoint C k
  disjoint D x
  disjoint E x
  disjoint k ph
  disjoint G x
  disjoint H x
  disjoint X x
  assert |- ( ph -> ( H gsum ( k e. A |-> D ) ) = E )

  proof
    wph
    cH
    vx
    cB
    cC
    cmpt
    #
    vk
    cA
    cX
    cmpt
    #
    ccom
    #
    cgsu
    co
    cG
    @1
    cgsu
    co
    #
    @0
    cfv
    #
    cH
    vk
    cA
    cD
    cmpt
    #
    cgsu
    co
    cE
    wph
    cA
    cB
    @1
    cG
    cH
    @0
    cV
    c.0
    gsummhm2.b
    gsummhm2.z
    gsummhm2.g
    gsummhm2.h
    gsummhm2.a
    gsummhm2.k
    wph
    vk
    cA
    cX
    cB
    @1
    gsummhm2.f
    @1
    eqid
    fmptd
    #
    gsummhm2.w
    gsummhm
    wph
    @2
    @5
    cH
    cgsu
    wph
    vk
    vx
    cA
    cB
    cX
    cC
    cD
    @1
    @0
    gsummhm2.f
    wph
    @1
    eqidd
    wph
    @0
    eqidd
    gsummhm2.1
    fmptco
    oveq2d
    wph
    @3
    cB
    wcel
    #
    cE
    cH
    cbs
    cfv
    #
    wcel
    #
    @4
    cE
    wceq
    wph
    cA
    cB
    @1
    cG
    cV
    c.0
    gsummhm2.b
    gsummhm2.z
    gsummhm2.g
    gsummhm2.a
    @6
    gsummhm2.w
    gsumcl
    #
    wph
    @7
    cC
    @8
    wcel
    #
    vx
    cB
    wral
    #
    @9
    @10
    wph
    cB
    @8
    @0
    wf
    #
    @12
    wph
    @0
    cG
    cH
    cmhm
    co
    wcel
    @13
    gsummhm2.k
    cB
    @8
    cG
    cH
    @0
    gsummhm2.b
    @8
    eqid
    mhmf
    syl
    vx
    cB
    @8
    cC
    @0
    @0
    eqid
    #
    fmpt
    sylibr
    @11
    @9
    vx
    @3
    cB
    vx
    cv
    @3
    wceq
    cC
    cE
    @8
    gsummhm2.2
    eleq1d
    rspcv
    sylc
    vx
    @3
    cC
    cE
    cB
    @8
    @0
    gsummhm2.2
    @14
    fvmptg
    syl2anc
    3eqtr3d
end
