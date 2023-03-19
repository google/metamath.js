include "cfn.mm"
include "fmptd.mm"
include "cvv.mm"
include "wcel.mm"
include "c0g.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fsuppmptdm.mm"
include "gsuminv.mm"

theorem gsummptfidminv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cI: class I
  let c.0: class .0.
  assume gsuminv.b: |- B = ( Base ` G )
  assume gsuminv.z: |- .0. = ( 0g ` G )
  assume gsuminv.p: |- I = ( invg ` G )
  assume gsuminv.g: |- ( ph -> G e. Abel )
  assume gsummptfidminv.a: |- ( ph -> A e. Fin )
  assume gsummptfidminv.c: |- ( ( ph /\ x e. A ) -> C e. B )
  assume gsummptfidminv.f: |- F = ( x e. A |-> C )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> ( G gsum ( I o. F ) ) = ( I ` ( G gsum F ) ) )

  proof
    wph
    cA
    cB
    cF
    cG
    cI
    cfn
    c.0
    gsuminv.b
    gsuminv.z
    gsuminv.p
    gsuminv.g
    gsummptfidminv.a
    wph
    vx
    cA
    cC
    cB
    cF
    gsummptfidminv.c
    gsummptfidminv.f
    fmptd
    wph
    vx
    cA
    cF
    cB
    cvv
    cC
    c.0
    gsummptfidminv.f
    gsummptfidminv.a
    gsummptfidminv.c
    c.0
    cvv
    wcel
    wph
    c.0
    cG
    c0g
    cfv
    cvv
    gsuminv.z
    cG
    c0g
    fvex
    eqeltri
    a1i
    fsuppmptdm
    gsuminv
end
