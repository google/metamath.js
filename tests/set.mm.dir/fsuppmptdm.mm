include "fmptd.mm"
include "fdmfifsupp.mm"

theorem fsuppmptdm
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cV: class V
  let cW: class W
  let cY: class Y
  let cZ: class Z
  assume fsuppmptdm.f: |- F = ( x e. A |-> Y )
  assume fsuppmptdm.a: |- ( ph -> A e. Fin )
  assume fsuppmptdm.y: |- ( ( ph /\ x e. A ) -> Y e. V )
  assume fsuppmptdm.z: |- ( ph -> Z e. W )

  disjoint A x
  disjoint V x
  disjoint ph x
  assert |- ( ph -> F finSupp Z )

  proof
    wph
    cA
    cV
    cF
    cW
    cZ
    wph
    vx
    cA
    cY
    cV
    cF
    fsuppmptdm.y
    fsuppmptdm.f
    fmptd
    fsuppmptdm.a
    fsuppmptdm.z
    fdmfifsupp
end
