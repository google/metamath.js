include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "wral.mm"
include "cuni.mm"
include "cmap.mm"
include "crab.mm"
include "cvv.mm"
include "ctopon.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "jctr.mm"
include "istopon.mm"
include "sylibr.mm"
include "cnfval.mm"
include "syl2an.mm"
include "wf.mm"
include "cab.mm"
include "uniexg.mm"
include "mapvalg.mm"
include "syl2anr.mm"
include "mapex.mm"
include "eqeltrd.mm"
include "rabexg.mm"
include "syl.mm"

theorem cnfex
  let cJ: class J
  let cK: class K
  let vf: setvar f
  let vy: setvar y


  assert |- ( ( J e. Top /\ K e. Top ) -> ( J Cn K ) e. _V )

  proof
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    wa
    #
    cJ
    cK
    ccn
    co
    #
    vf
    cv
    #
    ccnv
    vy
    cv
    cima
    cJ
    wcel
    vy
    cK
    wral
    #
    vf
    cK
    cuni
    #
    cJ
    cuni
    #
    cmap
    co
    #
    crab
    #
    cvv
    @0
    cJ
    @7
    ctopon
    cfv
    wcel
    #
    cK
    @6
    ctopon
    cfv
    wcel
    #
    @3
    @9
    wceq
    @1
    @0
    @0
    @7
    @7
    wceq
    #
    wa
    @10
    @0
    @12
    @7
    eqid
    jctr
    @7
    cJ
    istopon
    sylibr
    @1
    @1
    @6
    @6
    wceq
    #
    wa
    @11
    @1
    @13
    @6
    eqid
    jctr
    @6
    cK
    istopon
    sylibr
    vy
    vf
    cJ
    cK
    @7
    @6
    cnfval
    syl2an
    @2
    @8
    cvv
    wcel
    @9
    cvv
    wcel
    @2
    @8
    @7
    @6
    @4
    wf
    vf
    cab
    #
    cvv
    @1
    @6
    cvv
    wcel
    #
    @7
    cvv
    wcel
    #
    @8
    @14
    wceq
    @0
    cK
    ctop
    uniexg
    #
    cJ
    ctop
    uniexg
    #
    @6
    @7
    cvv
    cvv
    vf
    mapvalg
    syl2anr
    @0
    @16
    @15
    @14
    cvv
    wcel
    @1
    @18
    @17
    @7
    @6
    cvv
    cvv
    vf
    mapex
    syl2an
    eqeltrd
    @5
    vf
    @8
    cvv
    rabexg
    syl
    eqeltrd
end
