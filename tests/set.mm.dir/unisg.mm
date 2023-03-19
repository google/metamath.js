include "wcel.mm"
include "cuni.mm"
include "csigagen.mm"
include "cfv.mm"
include "csiga.mm"
include "crn.mm"
include "wceq.mm"
include "wa.mm"
include "sigagensiga.mm"
include "issgon.mm"
include "sylib.mm"
include "simprd.mm"
include "eqcomd.mm"

theorem unisg
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> U. ( sigaGen ` A ) = U. A )

  proof
    cA
    cV
    wcel
    #
    cA
    cuni
    #
    cA
    csigagen
    cfv
    #
    cuni
    #
    @0
    @2
    csiga
    crn
    cuni
    wcel
    #
    @1
    @3
    wceq
    #
    @0
    @2
    @1
    csiga
    cfv
    wcel
    @4
    @5
    wa
    cA
    cV
    sigagensiga
    @2
    @1
    issgon
    sylib
    simprd
    eqcomd
end
