include "cwwspthsnon.mm"
include "co.mm"
include "wcel.mm"
include "cn0.mm"
include "cvv.mm"
include "wa.mm"
include "cvtx.mm"
include "cfv.mm"
include "cwwlksnon.mm"
include "cv.mm"
include "cspthson.mm"
include "wbr.mm"
include "wex.mm"
include "w3a.mm"
include "wceq.mm"
include "eqid.mm"
include "wspthnonp.mm"
include "simp3r.mm"
include "wi.mm"
include "cpthson.mm"
include "cwlkson.mm"
include "spthonpthon.mm"
include "anim12i.mm"
include "ctrlson.mm"
include "pthontrlon.mm"
include "trlsonwlkon.mm"
include "syl2an.mm"
include "wlksoneq1eq2.mm"
include "3syl.mm"
include "expcom.mm"
include "exlimiv.mm"
include "com12.mm"
include "imp.mm"

theorem wspthneq1eq2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cN: class N
  let vf: setvar f
  let vh: setvar h


  assert |- ( ( P e. ( A ( N WSPathsNOn G ) B ) /\ P e. ( C ( N WSPathsNOn G ) D ) ) -> ( A = C /\ B = D ) )

  proof
    cP
    cA
    cB
    cN
    cG
    cwwspthsnon
    co
    #
    co
    wcel
    cN
    cn0
    wcel
    cG
    cvv
    wcel
    wa
    #
    cA
    cG
    cvtx
    cfv
    #
    wcel
    cB
    @2
    wcel
    wa
    #
    cP
    cA
    cB
    cN
    cG
    cwwlksnon
    co
    #
    co
    wcel
    #
    vf
    cv
    #
    cP
    cA
    cB
    cG
    cspthson
    cfv
    #
    co
    wbr
    #
    vf
    wex
    #
    wa
    w3a
    #
    @1
    cC
    @2
    wcel
    cD
    @2
    wcel
    wa
    #
    cP
    cC
    cD
    @4
    co
    wcel
    #
    vh
    cv
    #
    cP
    cC
    cD
    @7
    co
    wbr
    #
    vh
    wex
    #
    wa
    w3a
    #
    cA
    cC
    wceq
    cB
    cD
    wceq
    wa
    #
    cP
    cC
    cD
    @0
    co
    wcel
    cA
    cB
    vf
    cG
    cN
    @2
    cP
    @2
    eqid
    #
    wspthnonp
    cC
    cD
    vh
    cG
    cN
    @2
    cP
    @18
    wspthnonp
    @10
    @9
    @15
    @17
    @16
    @1
    @3
    @5
    @9
    simp3r
    @1
    @11
    @12
    @15
    simp3r
    @9
    @15
    @17
    @8
    @15
    @17
    wi
    vf
    @15
    @8
    @17
    @14
    @8
    @17
    wi
    vh
    @8
    @14
    @17
    @8
    @14
    wa
    @6
    cP
    cA
    cB
    cG
    cpthson
    cfv
    #
    co
    wbr
    #
    @13
    cP
    cC
    cD
    @19
    co
    wbr
    #
    wa
    @6
    cP
    cA
    cB
    cG
    cwlkson
    cfv
    #
    co
    wbr
    #
    @13
    cP
    cC
    cD
    @22
    co
    wbr
    #
    wa
    #
    @17
    @8
    @20
    @14
    @21
    cA
    cB
    cP
    @6
    cG
    spthonpthon
    cC
    cD
    cP
    @13
    cG
    spthonpthon
    anim12i
    @20
    @6
    cP
    cA
    cB
    cG
    ctrlson
    cfv
    #
    co
    wbr
    #
    @13
    cP
    cC
    cD
    @26
    co
    wbr
    #
    @25
    @21
    cA
    cB
    cP
    @6
    cG
    pthontrlon
    cC
    cD
    cP
    @13
    cG
    pthontrlon
    @27
    @23
    @28
    @24
    cA
    cB
    cP
    @6
    cG
    trlsonwlkon
    cC
    cD
    cP
    @13
    cG
    trlsonwlkon
    anim12i
    syl2an
    cA
    cB
    cC
    cD
    cP
    @6
    cG
    @13
    wlksoneq1eq2
    3syl
    expcom
    exlimiv
    com12
    exlimiv
    imp
    syl2an
    syl2an
end
