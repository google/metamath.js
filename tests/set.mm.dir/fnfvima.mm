include "wfn.mm"
include "wss.mm"
include "wcel.mm"
include "w3a.mm"
include "wfun.mm"
include "cdm.mm"
include "wa.mm"
include "cfv.mm"
include "cima.mm"
include "fnfun.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "wceq.mm"
include "fndm.mm"
include "sseqtr4d.mm"
include "jca.mm"
include "simp3.mm"
include "funfvima2.mm"
include "sylc.mm"

theorem fnfvima
  let cA: class A
  let cS: class S
  let cF: class F
  let cX: class X


  assert |- ( ( F Fn A /\ S C_ A /\ X e. S ) -> ( F ` X ) e. ( F " S ) )

  proof
    cF
    cA
    wfn
    #
    cS
    cA
    wss
    #
    cX
    cS
    wcel
    #
    w3a
    #
    cF
    wfun
    #
    cS
    cF
    cdm
    #
    wss
    #
    wa
    @2
    cX
    cF
    cfv
    cF
    cS
    cima
    wcel
    @3
    @4
    @6
    @0
    @1
    @4
    @2
    cA
    cF
    fnfun
    3ad2ant1
    @3
    cS
    cA
    @5
    @0
    @1
    @2
    simp2
    @0
    @1
    @5
    cA
    wceq
    @2
    cA
    cF
    fndm
    3ad2ant1
    sseqtr4d
    jca
    @0
    @1
    @2
    simp3
    cS
    cX
    cF
    funfvima2
    sylc
end
