include "cv.mm"
include "crglmod.mm"
include "cfv.mm"
include "clnm.mm"
include "wcel.mm"
include "crg.mm"
include "clnr.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "df-lnr.mm"
include "elrab2.mm"

theorem islnr
  let cA: class A
  let va: setvar a


  assert |- ( A e. LNoeR <-> ( A e. Ring /\ ( ringLMod ` A ) e. LNoeM ) )

  proof
    va
    cv
    #
    crglmod
    cfv
    #
    clnm
    wcel
    cA
    crglmod
    cfv
    #
    clnm
    wcel
    va
    cA
    crg
    clnr
    @0
    cA
    wceq
    @1
    @2
    clnm
    @0
    cA
    crglmod
    fveq2
    eleq1d
    va
    df-lnr
    elrab2
end
