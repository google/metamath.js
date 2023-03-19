include "cuni.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cres.mm"
include "crest.mm"
include "co.mm"
include "chmeo.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "crab.mm"
include "cmpt.mm"
include "eqid.mm"
include "cvmopnlem.mm"

theorem cvmopn
  let cA: class A
  let cC: class C
  let cF: class F
  let cJ: class J
  let vu: setvar u
  let vv: setvar v
  let vk: setvar k
  let vs: setvar s


  assert |- ( ( F e. ( C CovMap J ) /\ A e. C ) -> ( F " A ) e. J )

  proof
    vv
    vu
    cA
    cC
    cuni
    #
    cC
    vk
    cJ
    vs
    cv
    #
    cuni
    cF
    ccnv
    vk
    cv
    #
    cima
    wceq
    vu
    cv
    #
    vv
    cv
    cin
    c0
    wceq
    vv
    @1
    @3
    csn
    cdif
    wral
    cF
    @3
    cres
    cC
    @3
    crest
    co
    cJ
    @2
    crest
    co
    chmeo
    co
    wcel
    wa
    vu
    @1
    wral
    wa
    vs
    cC
    cpw
    c0
    csn
    cdif
    crab
    cmpt
    #
    vk
    cF
    cJ
    vs
    @4
    eqid
    @0
    eqid
    cvmopnlem
end
