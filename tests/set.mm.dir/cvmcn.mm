include "ccvm.mm"
include "co.mm"
include "wcel.mm"
include "ctop.mm"
include "ccn.mm"
include "w3a.mm"
include "cv.mm"
include "cuni.mm"
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
include "chmeo.mm"
include "wa.mm"
include "cpw.mm"
include "crab.mm"
include "cmpt.mm"
include "cfv.mm"
include "wne.mm"
include "wrex.mm"
include "eqid.mm"
include "iscvm.mm"
include "simplbi.mm"
include "simp3d.mm"

theorem cvmcn
  let cC: class C
  let cF: class F
  let cJ: class J
  let vk: setvar k
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x


  assert |- ( F e. ( C CovMap J ) -> F e. ( C Cn J ) )

  proof
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    cC
    ctop
    wcel
    #
    cJ
    ctop
    wcel
    #
    cF
    cC
    cJ
    ccn
    co
    wcel
    #
    @0
    @1
    @2
    @3
    w3a
    vx
    cv
    vk
    cv
    #
    wcel
    @4
    vk
    cJ
    vs
    cv
    #
    cuni
    cF
    ccnv
    @4
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
    @5
    @6
    csn
    cdif
    wral
    cF
    @6
    cres
    cC
    @6
    crest
    co
    cJ
    @4
    crest
    co
    chmeo
    co
    wcel
    wa
    vu
    @5
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
    cfv
    c0
    wne
    wa
    vk
    cJ
    wrex
    vx
    cJ
    cuni
    #
    wral
    vx
    vv
    vu
    cC
    @7
    vk
    cF
    cJ
    @8
    vs
    @7
    eqid
    @8
    eqid
    iscvm
    simplbi
    simp3d
end
