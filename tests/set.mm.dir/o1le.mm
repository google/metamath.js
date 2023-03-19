include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "clo1.mm"
include "cvv.mm"
include "o1mptrcl.mm"
include "lo1o12.mm"
include "mpbid.mm"
include "cv.mm"
include "wa.mm"
include "fvexd.mm"
include "abscld.mm"
include "lo1le.mm"
include "mpbird.mm"

theorem o1le
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  let cV: class V
  assume o1le.1: |- ( ph -> M e. RR )
  assume o1le.2: |- ( ph -> ( x e. A |-> B ) e. O(1) )
  assume o1le.3: |- ( ( ph /\ x e. A ) -> B e. V )
  assume o1le.4: |- ( ( ph /\ x e. A ) -> C e. CC )
  assume o1le.5: |- ( ( ph /\ ( x e. A /\ M <_ x ) ) -> ( abs ` C ) <_ ( abs ` B ) )

  disjoint A x
  disjoint M x
  disjoint ph x
  assert |- ( ph -> ( x e. A |-> C ) e. O(1) )

  proof
    wph
    vx
    cA
    cC
    cmpt
    co1
    wcel
    vx
    cA
    cC
    cabs
    cfv
    #
    cmpt
    clo1
    wcel
    wph
    vx
    cA
    cB
    cabs
    cfv
    #
    @0
    cM
    cvv
    o1le.1
    wph
    vx
    cA
    cB
    cmpt
    co1
    wcel
    vx
    cA
    @1
    cmpt
    clo1
    wcel
    o1le.2
    wph
    vx
    cA
    cB
    wph
    vx
    cA
    cB
    cV
    o1le.3
    o1le.2
    o1mptrcl
    lo1o12
    mpbid
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    cB
    cabs
    fvexd
    @2
    cC
    o1le.4
    abscld
    o1le.5
    lo1le
    wph
    vx
    cA
    cC
    o1le.4
    lo1o12
    mpbird
end
