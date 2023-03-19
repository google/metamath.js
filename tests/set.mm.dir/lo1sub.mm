include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "cmin.mm"
include "clo1.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "lo1mptrcl.mm"
include "recnd.mm"
include "negsubd.mm"
include "mpteq2dva.mm"
include "cr.mm"
include "renegcld.mm"
include "co1.mm"
include "o1lo1.mm"
include "mpbid.mm"
include "simprd.mm"
include "lo1add.mm"
include "eqeltrrd.mm"

theorem lo1sub
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume lo1sub.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume lo1sub.2: |- ( ( ph /\ x e. A ) -> C e. RR )
  assume lo1sub.3: |- ( ph -> ( x e. A |-> B ) e. <_O(1) )
  assume lo1sub.4: |- ( ph -> ( x e. A |-> C ) e. O(1) )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> ( x e. A |-> ( B - C ) ) e. <_O(1) )

  proof
    wph
    vx
    cA
    cB
    cC
    cneg
    #
    caddc
    co
    #
    cmpt
    vx
    cA
    cB
    cC
    cmin
    co
    #
    cmpt
    clo1
    wph
    vx
    cA
    @1
    @2
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    cB
    cC
    @3
    cB
    wph
    vx
    cA
    cB
    cV
    lo1sub.1
    lo1sub.3
    lo1mptrcl
    #
    recnd
    @3
    cC
    lo1sub.2
    recnd
    negsubd
    mpteq2dva
    wph
    vx
    cA
    cB
    @0
    cr
    @4
    @3
    cC
    lo1sub.2
    renegcld
    lo1sub.3
    wph
    vx
    cA
    cC
    cmpt
    #
    clo1
    wcel
    #
    vx
    cA
    @0
    cmpt
    clo1
    wcel
    #
    wph
    @5
    co1
    wcel
    @6
    @7
    wa
    lo1sub.4
    wph
    vx
    cA
    cC
    lo1sub.2
    o1lo1
    mpbid
    simprd
    lo1add
    eqeltrrd
end
