include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "w3a.mm"
include "cint.mm"
include "wa.mm"
include "cfi.mm"
include "elfir.mm"
include "wceq.mm"
include "filfi.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "fileln0.mm"
include "syldan.mm"

theorem filintn0
  let cA: class A
  let cF: class F
  let cX: class X


  assert |- ( ( F e. ( Fil ` X ) /\ ( A C_ F /\ A =/= (/) /\ A e. Fin ) ) -> |^| A =/= (/) )

  proof
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    cA
    cF
    wss
    cA
    c0
    wne
    cA
    cfn
    wcel
    w3a
    #
    cA
    cint
    #
    cF
    wcel
    @3
    c0
    wne
    @1
    @2
    wa
    @3
    cF
    cfi
    cfv
    #
    cF
    cA
    cF
    @0
    elfir
    @1
    @4
    cF
    wceq
    @2
    cF
    cX
    filfi
    adantr
    eleqtrd
    @3
    cF
    cX
    fileln0
    syldan
end
