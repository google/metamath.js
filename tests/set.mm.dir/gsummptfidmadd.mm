include "cfn.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "cvv.mm"
include "fvexd.mm"
include "fsuppmptdm.mm"
include "gsummptfsadd.mm"

theorem gsummptfidmadd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cH: class H
  assume gsummptfidmadd.b: |- B = ( Base ` G )
  assume gsummptfidmadd.p: |- .+ = ( +g ` G )
  assume gsummptfidmadd.g: |- ( ph -> G e. CMnd )
  assume gsummptfidmadd.a: |- ( ph -> A e. Fin )
  assume gsummptfidmadd.c: |- ( ( ph /\ x e. A ) -> C e. B )
  assume gsummptfidmadd.d: |- ( ( ph /\ x e. A ) -> D e. B )
  assume gsummptfidmadd.f: |- F = ( x e. A |-> C )
  assume gsummptfidmadd.h: |- H = ( x e. A |-> D )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint .+ x
  assert |- ( ph -> ( G gsum ( x e. A |-> ( C .+ D ) ) ) = ( ( G gsum F ) .+ ( G gsum H ) ) )

  proof
    wph
    vx
    cA
    cB
    cC
    cD
    c.pl
    cF
    cG
    cH
    cfn
    cG
    c0g
    cfv
    #
    gsummptfidmadd.b
    @0
    eqid
    gsummptfidmadd.p
    gsummptfidmadd.g
    gsummptfidmadd.a
    gsummptfidmadd.c
    gsummptfidmadd.d
    cF
    vx
    cA
    cC
    cmpt
    wceq
    wph
    gsummptfidmadd.f
    a1i
    cH
    vx
    cA
    cD
    cmpt
    wceq
    wph
    gsummptfidmadd.h
    a1i
    wph
    vx
    cA
    cF
    cB
    cvv
    cC
    @0
    gsummptfidmadd.f
    gsummptfidmadd.a
    gsummptfidmadd.c
    wph
    cG
    c0g
    fvexd
    #
    fsuppmptdm
    wph
    vx
    cA
    cH
    cB
    cvv
    cD
    @0
    gsummptfidmadd.h
    gsummptfidmadd.a
    gsummptfidmadd.d
    @1
    fsuppmptdm
    gsummptfsadd
end
