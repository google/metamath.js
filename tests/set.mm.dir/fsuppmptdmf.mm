include "fmptdf.mm"
include "fdmfifsupp.mm"

theorem fsuppmptdmf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cV: class V
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vk: setvar k
  assume fsuppmptdmf.n: |- F/ x ph
  assume fsuppmptdmf.f: |- F = ( x e. A |-> Y )
  assume fsuppmptdmf.a: |- ( ph -> A e. Fin )
  assume fsuppmptdmf.y: |- ( ( ph /\ x e. A ) -> Y e. V )
  assume fsuppmptdmf.z: |- ( ph -> Z e. W )

  disjoint A x
  disjoint V x
  disjoint k x
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
    fsuppmptdmf.n
    fsuppmptdmf.y
    fsuppmptdmf.f
    fmptdf
    fsuppmptdmf.a
    fsuppmptdmf.z
    fdmfifsupp
end
