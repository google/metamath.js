include "cssc.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "cdm.mm"
include "cxp.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "simpl.mm"
include "eqidd.mm"
include "sscfn1.mm"
include "simpr.mm"
include "ssc1.mm"
include "eqssd.mm"
include "sqxpeqd.mm"
include "wcel.mm"
include "wfn.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "ssc2.mm"
include "wss.mm"
include "sseldd.mm"
include "ralrimivva.mm"
include "wb.mm"
include "eqfnov.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem ssceq
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cH: class H
  let cS: class S
  let cT: class T


  assert |- ( ( A C_cat B /\ B C_cat A ) -> A = B )

  proof
    cA
    cB
    cssc
    wbr
    #
    cB
    cA
    cssc
    wbr
    #
    wa
    #
    cA
    cB
    wceq
    #
    cA
    cdm
    cdm
    #
    @4
    cxp
    #
    cB
    cdm
    cdm
    #
    @6
    cxp
    #
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    cA
    co
    #
    @9
    @10
    cB
    co
    #
    wceq
    #
    vy
    @4
    wral
    vx
    @4
    wral
    #
    @2
    @4
    @6
    @2
    @4
    @6
    @2
    @4
    @6
    cA
    cB
    @2
    @4
    cA
    cB
    @0
    @1
    simpl
    #
    @2
    @4
    eqidd
    sscfn1
    #
    @2
    @6
    cB
    cA
    @0
    @1
    simpr
    #
    @2
    @6
    eqidd
    sscfn1
    #
    @15
    ssc1
    #
    @2
    @6
    @4
    cB
    cA
    @18
    @16
    @17
    ssc1
    eqssd
    sqxpeqd
    @2
    @13
    vx
    vy
    @4
    @4
    @2
    @9
    @4
    wcel
    #
    @10
    @4
    wcel
    #
    wa
    #
    wa
    #
    @11
    @12
    @23
    @4
    cA
    cB
    @9
    @10
    @2
    cA
    @5
    wfn
    #
    @22
    @16
    adantr
    @2
    @0
    @22
    @15
    adantr
    @2
    @20
    @21
    simprl
    #
    @2
    @20
    @21
    simprr
    #
    ssc2
    @23
    @6
    cB
    cA
    @9
    @10
    @2
    cB
    @7
    wfn
    #
    @22
    @18
    adantr
    @2
    @1
    @22
    @17
    adantr
    @23
    @4
    @6
    @9
    @2
    @4
    @6
    wss
    @22
    @19
    adantr
    #
    @25
    sseldd
    @23
    @4
    @6
    @10
    @28
    @26
    sseldd
    ssc2
    eqssd
    ralrimivva
    @2
    @24
    @27
    @3
    @8
    @14
    wa
    wb
    @16
    @18
    vx
    vy
    @4
    @4
    @6
    @6
    cA
    cB
    eqfnov
    syl2anc
    mpbir2and
end
