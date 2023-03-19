include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cab.mm"
include "wbr.mm"
include "csn.mm"
include "cima.mm"
include "eqcom.mm"
include "fnbrfvb.mm"
include "syl5bb.mm"
include "abbidv.mm"
include "df-sn.mm"
include "a1i.mm"
include "wrel.mm"
include "fnrel.mm"
include "relimasn.mm"
include "syl.mm"
include "adantr.mm"
include "3eqtr4d.mm"

theorem fnsnfv
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F Fn A /\ B e. A ) -> { ( F ` B ) } = ( F " { B } ) )

  proof
    cF
    cA
    wfn
    #
    cB
    cA
    wcel
    #
    wa
    #
    vy
    cv
    #
    cB
    cF
    cfv
    #
    wceq
    #
    vy
    cab
    #
    cB
    @3
    cF
    wbr
    #
    vy
    cab
    #
    @4
    csn
    #
    cF
    cB
    csn
    cima
    #
    @2
    @5
    @7
    vy
    @5
    @4
    @3
    wceq
    @2
    @7
    @3
    @4
    eqcom
    cA
    cB
    @3
    cF
    fnbrfvb
    syl5bb
    abbidv
    @9
    @6
    wceq
    @2
    vy
    @4
    df-sn
    a1i
    @0
    @10
    @8
    wceq
    #
    @1
    @0
    cF
    wrel
    @11
    cA
    cF
    fnrel
    vy
    cB
    cF
    relimasn
    syl
    adantr
    3eqtr4d
end
