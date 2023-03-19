include "cabs.mm"
include "cfv.mm"
include "cmpt.mm"
include "clo1.mm"
include "wcel.mm"
include "co1.mm"
include "cv.mm"
include "wa.mm"
include "abscld.mm"
include "cle.mm"
include "wbr.mm"
include "fveq2d.mm"
include "lo1eq.mm"
include "lo1o12.mm"
include "3bitr4d.mm"

theorem o1eq
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume rlimeq.1: |- ( ( ph /\ x e. A ) -> B e. CC )
  assume rlimeq.2: |- ( ( ph /\ x e. A ) -> C e. CC )
  assume rlimeq.3: |- ( ph -> D e. RR )
  assume rlimeq.4: |- ( ( ph /\ ( x e. A /\ D <_ x ) ) -> B = C )

  disjoint A x
  disjoint D x
  disjoint ph x
  assert |- ( ph -> ( ( x e. A |-> B ) e. O(1) <-> ( x e. A |-> C ) e. O(1) ) )

  proof
    wph
    vx
    cA
    cB
    cabs
    cfv
    #
    cmpt
    clo1
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
    vx
    cA
    cB
    cmpt
    co1
    wcel
    vx
    cA
    cC
    cmpt
    co1
    wcel
    wph
    vx
    cA
    @0
    @1
    cD
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    cB
    rlimeq.1
    abscld
    @4
    cC
    rlimeq.2
    abscld
    rlimeq.3
    wph
    @3
    cD
    @2
    cle
    wbr
    wa
    wa
    cB
    cC
    cabs
    rlimeq.4
    fveq2d
    lo1eq
    wph
    vx
    cA
    cB
    rlimeq.1
    lo1o12
    wph
    vx
    cA
    cC
    rlimeq.2
    lo1o12
    3bitr4d
end
