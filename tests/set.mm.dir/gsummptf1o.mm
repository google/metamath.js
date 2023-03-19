include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "ccom.mm"
include "cfn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "adantr.mm"
include "sseldd.mm"
include "eqid.mm"
include "fmptd.mm"
include "cvv.mm"
include "c0g.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fsuppmptdm.mm"
include "wral.mm"
include "wceq.mm"
include "wreu.mm"
include "wf1o.mm"
include "ralrimiva.mm"
include "f1ompt.mm"
include "sylanbrc.mm"
include "gsumf1o.mm"
include "csb.mm"
include "eqidd.mm"
include "fmptcos.mm"
include "nfv.mm"
include "wnfc.mm"
include "adantl.mm"
include "csbiedf.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "oveq2d.mm"

theorem gsummptf1o
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let c.0: class .0.
  assume gsummptf1o.x: |- F/_ x H
  assume gsummptf1o.b: |- B = ( Base ` G )
  assume gsummptf1o.z: |- .0. = ( 0g ` G )
  assume gsummptf1o.i: |- ( x = E -> C = H )
  assume gsummptf1o.g: |- ( ph -> G e. CMnd )
  assume gsummptf1o.a: |- ( ph -> A e. Fin )
  assume gsummptf1o.d: |- ( ph -> F C_ B )
  assume gsummptf1o.f: |- ( ( ph /\ x e. A ) -> C e. F )
  assume gsummptf1o.e: |- ( ( ph /\ y e. D ) -> E e. A )
  assume gsummptf1o.h: |- ( ( ph /\ x e. A ) -> E! y e. D x = E )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint E x
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( G gsum ( x e. A |-> C ) ) = ( G gsum ( y e. D |-> H ) ) )

  proof
    wph
    cG
    vx
    cA
    cC
    cmpt
    #
    cgsu
    co
    cG
    @0
    vy
    cD
    cE
    cmpt
    #
    ccom
    #
    cgsu
    co
    cG
    vy
    cD
    cH
    cmpt
    #
    cgsu
    co
    wph
    cA
    cB
    cD
    @0
    cG
    @1
    cfn
    c.0
    gsummptf1o.b
    gsummptf1o.z
    gsummptf1o.g
    gsummptf1o.a
    wph
    vx
    cA
    cC
    cB
    @0
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    cF
    cB
    cC
    wph
    cF
    cB
    wss
    @5
    gsummptf1o.d
    adantr
    gsummptf1o.f
    sseldd
    #
    @0
    eqid
    #
    fmptd
    wph
    vx
    cA
    @0
    cB
    cvv
    cC
    c.0
    @7
    gsummptf1o.a
    @6
    c.0
    cvv
    wcel
    wph
    c.0
    cG
    c0g
    cfv
    cvv
    gsummptf1o.z
    cG
    c0g
    fvex
    eqeltri
    a1i
    fsuppmptdm
    wph
    cE
    cA
    wcel
    #
    vy
    cD
    wral
    @4
    cE
    wceq
    #
    vy
    cD
    wreu
    #
    vx
    cA
    wral
    cD
    cA
    @1
    wf1o
    wph
    @8
    vy
    cD
    gsummptf1o.e
    ralrimiva
    #
    wph
    @10
    vx
    cA
    gsummptf1o.h
    ralrimiva
    vy
    vx
    cD
    cA
    cE
    @1
    @1
    eqid
    f1ompt
    sylanbrc
    gsumf1o
    wph
    @2
    @3
    cG
    cgsu
    wph
    @2
    vy
    cD
    vx
    cE
    cC
    csb
    #
    cmpt
    @3
    wph
    vy
    vx
    cD
    cA
    cE
    cC
    @1
    @0
    @11
    wph
    @1
    eqidd
    wph
    @0
    eqidd
    fmptcos
    wph
    vy
    cD
    @12
    cH
    wph
    vy
    cv
    cD
    wcel
    wa
    #
    vx
    cE
    cC
    cH
    cA
    @13
    vx
    nfv
    vx
    cH
    wnfc
    @13
    gsummptf1o.x
    a1i
    gsummptf1o.e
    @9
    cC
    cH
    wceq
    @13
    gsummptf1o.i
    adantl
    csbiedf
    mpteq2dva
    eqtrd
    oveq2d
    eqtrd
end
