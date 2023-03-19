include "cof.mm"
include "co.mm"
include "cgsu.mm"
include "cmpt.mm"
include "cfn.mm"
include "wceq.mm"
include "a1i.mm"
include "offval2.mm"
include "oveq2d.mm"
include "gsummptfidmadd.mm"
include "eqtrd.mm"

theorem gsummptfidmadd2
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
  assert |- ( ph -> ( G gsum ( F oF .+ H ) ) = ( ( G gsum F ) .+ ( G gsum H ) ) )

  proof
    wph
    cG
    cF
    cH
    c.pl
    cof
    co
    #
    cgsu
    co
    cG
    vx
    cA
    cC
    cD
    c.pl
    co
    cmpt
    #
    cgsu
    co
    cG
    cF
    cgsu
    co
    cG
    cH
    cgsu
    co
    c.pl
    co
    wph
    @0
    @1
    cG
    cgsu
    wph
    vx
    cA
    cC
    cD
    c.pl
    cF
    cH
    cfn
    cB
    cB
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
    offval2
    oveq2d
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
    gsummptfidmadd.b
    gsummptfidmadd.p
    gsummptfidmadd.g
    gsummptfidmadd.a
    gsummptfidmadd.c
    gsummptfidmadd.d
    gsummptfidmadd.f
    gsummptfidmadd.h
    gsummptfidmadd
    eqtrd
end
