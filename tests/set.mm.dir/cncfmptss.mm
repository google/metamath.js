include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cres.mm"
include "ccncf.mm"
include "co.mm"
include "resmptd.mm"
include "wcel.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "wceq.mm"
include "nfcv.mm"
include "nffv.mm"
include "fveq2.mm"
include "cbvmpt.mm"
include "a1i.mm"
include "3eqtr4rd.mm"
include "wss.mm"
include "rescncf.mm"
include "sylc.mm"
include "eqeltrd.mm"

theorem cncfmptss
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vy: setvar y
  assume cncfmptss.1: |- F/_ x F
  assume cncfmptss.2: |- ( ph -> F e. ( A -cn-> B ) )
  assume cncfmptss.3: |- ( ph -> C C_ A )

  disjoint C x
  disjoint x y
  disjoint C y
  disjoint A y
  disjoint F y
  assert |- ( ph -> ( x e. C |-> ( F ` x ) ) e. ( C -cn-> B ) )

  proof
    wph
    vx
    cC
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    cF
    cC
    cres
    #
    cC
    cB
    ccncf
    co
    #
    wph
    vy
    cA
    vy
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    cC
    cres
    vy
    cC
    @6
    cmpt
    #
    @3
    @2
    wph
    vy
    cA
    cC
    @6
    cncfmptss.3
    resmptd
    wph
    cF
    @7
    cC
    wph
    vy
    cA
    cB
    cF
    wph
    cF
    cA
    cB
    ccncf
    co
    wcel
    #
    cA
    cB
    cF
    wf
    cncfmptss.2
    cA
    cB
    cF
    cncff
    syl
    feqmptd
    reseq1d
    @2
    @8
    wceq
    wph
    vx
    vy
    cC
    @1
    @6
    vy
    @0
    cF
    vy
    cF
    nfcv
    vy
    @0
    nfcv
    nffv
    vx
    @5
    cF
    cncfmptss.1
    vx
    @5
    nfcv
    nffv
    @0
    @5
    cF
    fveq2
    cbvmpt
    a1i
    3eqtr4rd
    wph
    cC
    cA
    wss
    @9
    @3
    @4
    wcel
    cncfmptss.3
    cncfmptss.2
    cA
    cB
    cC
    cF
    rescncf
    sylc
    eqeltrd
end
