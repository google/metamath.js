include "csu.mm"
include "cmpt.mm"
include "cv.mm"
include "csb.mm"
include "ccn.mm"
include "co.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfsum.mm"
include "weq.mm"
include "csbeq1a.mm"
include "sumeq2sdv.mm"
include "cbvmpt.mm"
include "wcel.mm"
include "wa.mm"
include "syl5eqelr.mm"
include "fsumcn.mm"
include "syl5eqel.mm"

theorem fsumcnf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cJ: class J
  let cK: class K
  let cX: class X
  let vy: setvar y
  assume fsumcnf.1: |- K = ( TopOpen ` CCfld )
  assume fsumcnf.2: |- ( ph -> J e. ( TopOn ` X ) )
  assume fsumcnf.3: |- ( ph -> A e. Fin )
  assume fsumcnf.4: |- ( ( ph /\ k e. A ) -> ( x e. X |-> B ) e. ( J Cn K ) )

  disjoint k x
  disjoint A k
  disjoint A x
  disjoint J k
  disjoint K k
  disjoint X k
  disjoint X x
  disjoint k ph
  disjoint k y
  disjoint x y
  disjoint A y
  disjoint J y
  disjoint K y
  disjoint X y
  disjoint ph y
  disjoint B y
  assert |- ( ph -> ( x e. X |-> sum_ k e. A B ) e. ( J Cn K ) )

  proof
    wph
    vx
    cX
    cA
    cB
    vk
    csu
    #
    cmpt
    vy
    cX
    cA
    vx
    vy
    cv
    #
    cB
    csb
    #
    vk
    csu
    #
    cmpt
    cJ
    cK
    ccn
    co
    #
    vx
    vy
    cX
    @0
    @3
    vy
    @0
    nfcv
    vx
    cA
    @2
    vk
    vx
    cA
    nfcv
    vx
    @1
    cB
    nfcsb1v
    #
    nfsum
    vx
    vy
    weq
    cA
    cB
    @2
    vk
    vx
    @1
    cB
    csbeq1a
    #
    sumeq2sdv
    cbvmpt
    wph
    vy
    cA
    @2
    vk
    cJ
    cK
    cX
    fsumcnf.1
    fsumcnf.2
    fsumcnf.3
    wph
    vk
    cv
    cA
    wcel
    wa
    vy
    cX
    @2
    cmpt
    vx
    cX
    cB
    cmpt
    @4
    vx
    vy
    cX
    cB
    @2
    vy
    cB
    nfcv
    @5
    @6
    cbvmpt
    fsumcnf.4
    syl5eqelr
    fsumcn
    syl5eqel
end
