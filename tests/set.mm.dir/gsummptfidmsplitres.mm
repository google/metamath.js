include "cfn.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "fmptd.mm"
include "cvv.mm"
include "fvexd.mm"
include "fsuppmptdm.mm"
include "gsumsplit.mm"

theorem gsummptfidmsplitres
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cY: class Y
  assume gsummptfidmsplit.b: |- B = ( Base ` G )
  assume gsummptfidmsplit.p: |- .+ = ( +g ` G )
  assume gsummptfidmsplit.g: |- ( ph -> G e. CMnd )
  assume gsummptfidmsplit.a: |- ( ph -> A e. Fin )
  assume gsummptfidmsplit.y: |- ( ( ph /\ k e. A ) -> Y e. B )
  assume gsummptfidmsplit.i: |- ( ph -> ( C i^i D ) = (/) )
  assume gsummptfidmsplit.u: |- ( ph -> A = ( C u. D ) )
  assume gsummptfidmsplitres.f: |- F = ( k e. A |-> Y )

  disjoint A k
  disjoint B k
  disjoint C k
  disjoint D k
  disjoint k ph
  assert |- ( ph -> ( G gsum F ) = ( ( G gsum ( F |` C ) ) .+ ( G gsum ( F |` D ) ) ) )

  proof
    wph
    cA
    cB
    cC
    cD
    c.pl
    cF
    cG
    cfn
    cG
    c0g
    cfv
    #
    gsummptfidmsplit.b
    @0
    eqid
    gsummptfidmsplit.p
    gsummptfidmsplit.g
    gsummptfidmsplit.a
    wph
    vk
    cA
    cY
    cB
    cF
    gsummptfidmsplit.y
    gsummptfidmsplitres.f
    fmptd
    wph
    vk
    cA
    cF
    cB
    cvv
    cY
    @0
    gsummptfidmsplitres.f
    gsummptfidmsplit.a
    gsummptfidmsplit.y
    wph
    cG
    c0g
    fvexd
    fsuppmptdm
    gsummptfidmsplit.i
    gsummptfidmsplit.u
    gsumsplit
end
