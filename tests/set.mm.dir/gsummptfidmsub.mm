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
include "gsummptfssub.mm"

theorem gsummptfidmsub
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let c.mi: class .-
  assume gsummptfidmsub.b: |- B = ( Base ` G )
  assume gsummptfidmsub.s: |- .- = ( -g ` G )
  assume gsummptfidmsub.g: |- ( ph -> G e. Abel )
  assume gsummptfidmsub.a: |- ( ph -> A e. Fin )
  assume gsummptfidmsub.c: |- ( ( ph /\ x e. A ) -> C e. B )
  assume gsummptfidmsub.d: |- ( ( ph /\ x e. A ) -> D e. B )
  assume gsummptfidmsub.f: |- F = ( x e. A |-> C )
  assume gsummptfidmsub.h: |- H = ( x e. A |-> D )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint .- x
  assert |- ( ph -> ( G gsum ( x e. A |-> ( C .- D ) ) ) = ( ( G gsum F ) .- ( G gsum H ) ) )

  proof
    wph
    vx
    cA
    cB
    cC
    cD
    cF
    cG
    cH
    c.mi
    cfn
    cG
    c0g
    cfv
    #
    gsummptfidmsub.b
    @0
    eqid
    gsummptfidmsub.s
    gsummptfidmsub.g
    gsummptfidmsub.a
    gsummptfidmsub.c
    gsummptfidmsub.d
    cF
    vx
    cA
    cC
    cmpt
    wceq
    wph
    gsummptfidmsub.f
    a1i
    cH
    vx
    cA
    cD
    cmpt
    wceq
    wph
    gsummptfidmsub.h
    a1i
    wph
    vx
    cA
    cF
    cB
    cvv
    cC
    @0
    gsummptfidmsub.f
    gsummptfidmsub.a
    gsummptfidmsub.c
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
    gsummptfidmsub.h
    gsummptfidmsub.a
    gsummptfidmsub.d
    @1
    fsuppmptdm
    gsummptfssub
end
