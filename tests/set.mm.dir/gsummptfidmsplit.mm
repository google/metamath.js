include "cfn.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "cmpt.mm"
include "cvv.mm"
include "fvexd.mm"
include "fsuppmptdm.mm"
include "gsumsplit2.mm"

theorem gsummptfidmsplit
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let vk: setvar k
  let cG: class G
  let cY: class Y
  assume gsummptfidmsplit.b: |- B = ( Base ` G )
  assume gsummptfidmsplit.p: |- .+ = ( +g ` G )
  assume gsummptfidmsplit.g: |- ( ph -> G e. CMnd )
  assume gsummptfidmsplit.a: |- ( ph -> A e. Fin )
  assume gsummptfidmsplit.y: |- ( ( ph /\ k e. A ) -> Y e. B )
  assume gsummptfidmsplit.i: |- ( ph -> ( C i^i D ) = (/) )
  assume gsummptfidmsplit.u: |- ( ph -> A = ( C u. D ) )

  disjoint A k
  disjoint B k
  disjoint C k
  disjoint D k
  disjoint k ph
  assert |- ( ph -> ( G gsum ( k e. A |-> Y ) ) = ( ( G gsum ( k e. C |-> Y ) ) .+ ( G gsum ( k e. D |-> Y ) ) ) )

  proof
    wph
    cA
    cB
    cC
    cD
    c.pl
    vk
    cG
    cfn
    cY
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
    gsummptfidmsplit.y
    wph
    vk
    cA
    vk
    cA
    cY
    cmpt
    #
    cB
    cvv
    cY
    @0
    @1
    eqid
    gsummptfidmsplit.a
    gsummptfidmsplit.y
    wph
    cG
    c0g
    fvexd
    fsuppmptdm
    gsummptfidmsplit.i
    gsummptfidmsplit.u
    gsumsplit2
end
