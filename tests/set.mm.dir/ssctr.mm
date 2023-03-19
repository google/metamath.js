include "cssc.mm"
include "wbr.mm"
include "wa.mm"
include "cdm.mm"
include "wss.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "simpl.mm"
include "eqidd.mm"
include "sscfn1.mm"
include "sscfn2.mm"
include "ssc1.mm"
include "simpr.mm"
include "sstrd.mm"
include "wcel.mm"
include "cxp.mm"
include "wfn.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "ssc2.mm"
include "sseldd.mm"
include "ralrimivva.mm"
include "cvv.mm"
include "sscrel.mm"
include "brrelex2i.mm"
include "adantl.mm"
include "dmexg.mm"
include "3syl.mm"
include "isssc.mm"
include "mpbir2and.mm"

theorem ssctr
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let cH: class H
  let cS: class S
  let cT: class T


  assert |- ( ( A C_cat B /\ B C_cat C ) -> A C_cat C )

  proof
    cA
    cB
    cssc
    wbr
    #
    cB
    cC
    cssc
    wbr
    #
    wa
    #
    cA
    cC
    cssc
    wbr
    cA
    cdm
    cdm
    #
    cC
    cdm
    #
    cdm
    #
    wss
    vx
    cv
    #
    vy
    cv
    #
    cA
    co
    #
    @6
    @7
    cC
    co
    #
    wss
    #
    vy
    @3
    wral
    vx
    @3
    wral
    @2
    @3
    cB
    cdm
    cdm
    #
    @5
    @2
    @3
    @11
    cA
    cB
    @2
    @3
    cA
    cB
    @0
    @1
    simpl
    #
    @2
    @3
    eqidd
    sscfn1
    #
    @2
    @11
    cA
    cB
    @12
    @2
    @11
    eqidd
    sscfn2
    #
    @12
    ssc1
    #
    @2
    @11
    @5
    cB
    cC
    @14
    @2
    @5
    cB
    cC
    @0
    @1
    simpr
    #
    @2
    @5
    eqidd
    sscfn2
    #
    @16
    ssc1
    sstrd
    @2
    @10
    vx
    vy
    @3
    @3
    @2
    @6
    @3
    wcel
    #
    @7
    @3
    wcel
    #
    wa
    #
    wa
    #
    @8
    @6
    @7
    cB
    co
    @9
    @21
    @3
    cA
    cB
    @6
    @7
    @2
    cA
    @3
    @3
    cxp
    wfn
    @20
    @13
    adantr
    @2
    @0
    @20
    @12
    adantr
    @2
    @18
    @19
    simprl
    #
    @2
    @18
    @19
    simprr
    #
    ssc2
    @21
    @11
    cB
    cC
    @6
    @7
    @2
    cB
    @11
    @11
    cxp
    wfn
    @20
    @14
    adantr
    @2
    @1
    @20
    @16
    adantr
    @21
    @3
    @11
    @6
    @2
    @3
    @11
    wss
    @20
    @15
    adantr
    #
    @22
    sseldd
    @21
    @3
    @11
    @7
    @24
    @23
    sseldd
    ssc2
    sstrd
    ralrimivva
    @2
    vx
    vy
    @3
    @5
    cA
    cC
    cvv
    @13
    @17
    @2
    cC
    cvv
    wcel
    #
    @4
    cvv
    wcel
    @5
    cvv
    wcel
    @1
    @25
    @0
    cB
    cC
    cssc
    sscrel
    brrelex2i
    adantl
    cC
    cvv
    dmexg
    @4
    cvv
    dmexg
    3syl
    isssc
    mpbir2and
end
