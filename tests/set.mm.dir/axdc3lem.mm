include "com.mm"
include "cxp.mm"
include "cpw.mm"
include "dcomex.mm"
include "xpex.mm"
include "pwex.mm"
include "cv.mm"
include "csuc.mm"
include "wf.mm"
include "c0.mm"
include "cfv.mm"
include "wceq.mm"
include "wcel.mm"
include "wral.mm"
include "w3a.mm"
include "wrex.mm"
include "cab.mm"
include "wa.mm"
include "wss.mm"
include "fssxp.mm"
include "peano2.mm"
include "cvv.mm"
include "con0.mm"
include "omelon2.mm"
include "ax-mp.mm"
include "onelssi.mm"
include "xpss1.mm"
include "3syl.mm"
include "sylan9ss.mm"
include "selpw.mm"
include "sylibr.mm"
include "ancoms.mm"
include "3ad2antr1.mm"
include "rexlimiva.mm"
include "abssi.mm"
include "eqsstri.mm"
include "ssexi.mm"

theorem axdc3lem
  let cA: class A
  let cC: class C
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let vs: setvar s
  assume axdc3lem.1: |- A e. _V
  assume axdc3lem.2: |- S = { s | E. n e. _om ( s : suc n --> A /\ ( s ` (/) ) = C /\ A. k e. n ( s ` suc k ) e. ( F ` ( s ` k ) ) ) }

  disjoint A n
  disjoint A s
  disjoint n s
  assert |- S e. _V

  proof
    cS
    com
    cA
    cxp
    #
    cpw
    #
    @0
    com
    cA
    dcomex
    axdc3lem.1
    xpex
    pwex
    cS
    vn
    cv
    #
    csuc
    #
    cA
    vs
    cv
    #
    wf
    #
    c0
    @4
    cfv
    cC
    wceq
    #
    vk
    cv
    #
    csuc
    @4
    cfv
    @7
    @4
    cfv
    cF
    cfv
    wcel
    vk
    @2
    wral
    #
    w3a
    #
    vn
    com
    wrex
    #
    vs
    cab
    @1
    axdc3lem.2
    @10
    vs
    @1
    @9
    @4
    @1
    wcel
    #
    vn
    com
    @2
    com
    wcel
    #
    @6
    @5
    @11
    @8
    @5
    @12
    @11
    @5
    @12
    wa
    @4
    @0
    wss
    @11
    @5
    @12
    @4
    @3
    cA
    cxp
    #
    @0
    @3
    cA
    @4
    fssxp
    @12
    @3
    com
    wcel
    @3
    com
    wss
    @13
    @0
    wss
    @2
    peano2
    com
    @3
    com
    cvv
    wcel
    com
    con0
    wcel
    dcomex
    omelon2
    ax-mp
    onelssi
    @3
    com
    cA
    xpss1
    3syl
    sylan9ss
    vs
    @0
    selpw
    sylibr
    ancoms
    3ad2antr1
    rexlimiva
    abssi
    eqsstri
    ssexi
end
