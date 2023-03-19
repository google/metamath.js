include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cutop.mm"
include "cpw.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "crab.mm"
include "utopval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "sseq2.mm"
include "rexbidv.mm"
include "raleqbi1dv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "cvv.mm"
include "wi.mm"
include "elex.mm"
include "a1i.mm"
include "elfvex.mm"
include "adantr.mm"
include "simpr.mm"
include "ssexd.mm"
include "ex.mm"
include "wb.mm"
include "elpwg.mm"
include "pm5.21ndd.mm"
include "anbi1d.mm"
include "bitrd.mm"

theorem elutop
  let vx: setvar x
  let vv: setvar v
  let cA: class A
  let cU: class U
  let cX: class X
  let va: setvar a

  disjoint v x
  disjoint A v
  disjoint A x
  disjoint U v
  disjoint U x
  disjoint X x
  disjoint a v
  disjoint a x
  disjoint A a
  disjoint U a
  disjoint X a
  assert |- ( U e. ( UnifOn ` X ) -> ( A e. ( unifTop ` U ) <-> ( A C_ X /\ A. x e. A E. v e. U ( v " { x } ) C_ A ) ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cA
    cU
    cutop
    cfv
    #
    wcel
    #
    cA
    cX
    cpw
    #
    wcel
    #
    vv
    cv
    vx
    cv
    csn
    cima
    #
    cA
    wss
    #
    vv
    cU
    wrex
    #
    vx
    cA
    wral
    #
    wa
    #
    cA
    cX
    wss
    #
    @8
    wa
    @0
    @2
    cA
    @5
    va
    cv
    #
    wss
    #
    vv
    cU
    wrex
    #
    vx
    @11
    wral
    #
    va
    @3
    crab
    #
    wcel
    @9
    @0
    @1
    @15
    cA
    vx
    vv
    cU
    cX
    va
    utopval
    eleq2d
    @14
    @8
    va
    cA
    @3
    @13
    @7
    vx
    @11
    cA
    @11
    cA
    wceq
    @12
    @6
    vv
    cU
    @11
    cA
    @5
    sseq2
    rexbidv
    raleqbi1dv
    elrab
    syl6bb
    @0
    @4
    @10
    @8
    @0
    cA
    cvv
    wcel
    #
    @4
    @10
    @4
    @16
    wi
    @0
    cA
    @3
    elex
    a1i
    @0
    @10
    @16
    @0
    @10
    wa
    cA
    cX
    cvv
    @0
    cX
    cvv
    wcel
    @10
    cU
    cX
    cust
    elfvex
    adantr
    @0
    @10
    simpr
    ssexd
    ex
    @16
    @4
    @10
    wb
    wi
    @0
    cA
    cX
    cvv
    elpwg
    a1i
    pm5.21ndd
    anbi1d
    bitrd
end
