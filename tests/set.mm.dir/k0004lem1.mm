include "cin.mm"
include "wceq.mm"
include "wf.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "feq3.mm"
include "wfn.mm"
include "crn.mm"
include "fnima.mm"
include "sseq1d.mm"
include "anbi2d.mm"
include "ssin.mm"
include "syl6bb.mm"
include "pm5.32i.mm"
include "df-f.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "3bitr4i.mm"
include "syl6rbbr.mm"

theorem k0004lem1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( D = ( B i^i C ) -> ( ( F : A --> B /\ ( F " A ) C_ C ) <-> F : A --> D ) )

  proof
    cD
    cB
    cC
    cin
    #
    wceq
    cA
    cD
    cF
    wf
    cA
    @0
    cF
    wf
    #
    cA
    cB
    cF
    wf
    #
    cF
    cA
    cima
    #
    cC
    wss
    #
    wa
    #
    cD
    @0
    cA
    cF
    feq3
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cB
    wss
    #
    @4
    wa
    #
    wa
    #
    @6
    @7
    @0
    wss
    #
    wa
    @5
    @1
    @6
    @9
    @11
    @6
    @9
    @8
    @7
    cC
    wss
    #
    wa
    @11
    @6
    @4
    @12
    @8
    @6
    @3
    @7
    cC
    cA
    cF
    fnima
    sseq1d
    anbi2d
    @7
    cB
    cC
    ssin
    syl6bb
    pm5.32i
    @5
    @6
    @8
    wa
    #
    @4
    wa
    @10
    @2
    @13
    @4
    cA
    cB
    cF
    df-f
    anbi1i
    @6
    @8
    @4
    anass
    bitri
    cA
    @0
    cF
    df-f
    3bitr4i
    syl6rbbr
end
