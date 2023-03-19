include "cneg.mm"
include "cmpt.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "csmblfn.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "recnd.mm"
include "mulm1d.mm"
include "eqcomd.mm"
include "mpteq2da.mm"
include "cr.mm"
include "neg1rr.mm"
include "a1i.mm"
include "smfmulc1.mm"
include "eqeltrd.mm"

theorem smfneg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cV: class V
  let vk: setvar k
  assume smfneg.x: |- F/ x ph
  assume smfneg.s: |- ( ph -> S e. SAlg )
  assume smfneg.a: |- ( ph -> A e. V )
  assume smfneg.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume smfneg.m: |- ( ph -> ( x e. A |-> B ) e. ( SMblFn ` S ) )

  disjoint A x
  disjoint k x
  assert |- ( ph -> ( x e. A |-> -u B ) e. ( SMblFn ` S ) )

  proof
    wph
    vx
    cA
    cB
    cneg
    #
    cmpt
    vx
    cA
    c1
    cneg
    #
    cB
    cmul
    co
    #
    cmpt
    cS
    csmblfn
    cfv
    wph
    vx
    cA
    @0
    @2
    smfneg.x
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    @2
    @0
    @3
    cB
    @3
    cB
    smfneg.b
    recnd
    mulm1d
    eqcomd
    mpteq2da
    wph
    vx
    cA
    cB
    @1
    cS
    cV
    smfneg.x
    smfneg.s
    smfneg.a
    smfneg.b
    @1
    cr
    wcel
    wph
    neg1rr
    a1i
    smfneg.m
    smfmulc1
    eqeltrd
end
