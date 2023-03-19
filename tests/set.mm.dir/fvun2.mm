include "wfn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cun.mm"
include "cfv.mm"
include "uncom.mm"
include "fveq1i.mm"
include "incom.mm"
include "eqeq1i.mm"
include "anbi1i.mm"
include "fvun1.mm"
include "syl3an3b.mm"
include "3com12.mm"
include "syl5eq.mm"

theorem fvun2
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cX: class X


  assert |- ( ( F Fn A /\ G Fn B /\ ( ( A i^i B ) = (/) /\ X e. B ) ) -> ( ( F u. G ) ` X ) = ( G ` X ) )

  proof
    cF
    cA
    wfn
    #
    cG
    cB
    wfn
    #
    cA
    cB
    cin
    #
    c0
    wceq
    #
    cX
    cB
    wcel
    #
    wa
    #
    w3a
    cX
    cF
    cG
    cun
    #
    cfv
    cX
    cG
    cF
    cun
    #
    cfv
    #
    cX
    cG
    cfv
    #
    cX
    @6
    @7
    cF
    cG
    uncom
    fveq1i
    @1
    @0
    @5
    @8
    @9
    wceq
    #
    @5
    @1
    @0
    cB
    cA
    cin
    #
    c0
    wceq
    #
    @4
    wa
    @10
    @3
    @12
    @4
    @2
    @11
    c0
    cA
    cB
    incom
    eqeq1i
    anbi1i
    cB
    cA
    cG
    cF
    cX
    fvun1
    syl3an3b
    3com12
    syl5eq
end
