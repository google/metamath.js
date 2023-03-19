include "cc.mm"
include "wf.mm"
include "wcel.mm"
include "w3a.mm"
include "cvv.mm"
include "cc0.mm"
include "csupp.mm"
include "co.mm"
include "cfdiv.mm"
include "wss.mm"
include "cpm.mm"
include "cnex.mm"
include "a1i.mm"
include "simp3.mm"
include "fdivmptf.mm"
include "cdm.mm"
include "suppssdm.mm"
include "wceq.mm"
include "fdm.mm"
include "eqcomd.mm"
include "3ad2ant2.mm"
include "syl5sseqr.mm"
include "elpm2r.mm"
include "syl22anc.mm"

theorem fdivpm
  let cA: class A
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  let vk: setvar k


  assert |- ( ( F : A --> CC /\ G : A --> CC /\ A e. V ) -> ( F /_f G ) e. ( CC ^pm A ) )

  proof
    cA
    cc
    cF
    wf
    #
    cA
    cc
    cG
    wf
    #
    cA
    cV
    wcel
    #
    w3a
    #
    cc
    cvv
    wcel
    #
    @2
    cG
    cc0
    csupp
    co
    #
    cc
    cF
    cG
    cfdiv
    co
    #
    wf
    @5
    cA
    wss
    @6
    cc
    cA
    cpm
    co
    wcel
    @4
    @3
    cnex
    a1i
    @0
    @1
    @2
    simp3
    cA
    cF
    cG
    cV
    fdivmptf
    @3
    cG
    cdm
    #
    @5
    cA
    cG
    cc0
    suppssdm
    @1
    @0
    cA
    @7
    wceq
    @2
    @1
    @7
    cA
    cA
    cc
    cG
    fdm
    eqcomd
    3ad2ant2
    syl5sseqr
    cc
    cA
    @5
    @6
    cvv
    cV
    elpm2r
    syl22anc
end
