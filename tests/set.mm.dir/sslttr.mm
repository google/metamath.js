include "csslt.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wi.mm"
include "n0.mm"
include "cvv.mm"
include "csur.mm"
include "wss.mm"
include "cslt.mm"
include "wral.mm"
include "w3a.mm"
include "ssltex1.mm"
include "ssltex2.mm"
include "anim12i.mm"
include "adantl.mm"
include "ssltss1.mm"
include "ad2antrl.mm"
include "ssltss2.mm"
include "ad2antll.mm"
include "adantr.mm"
include "simprl.mm"
include "sseldd.mm"
include "simpll.mm"
include "simprr.mm"
include "ssltsep.mm"
include "rsp.mm"
include "sylc.mm"
include "slttrd.mm"
include "ralrimivva.mm"
include "3jca.mm"
include "brsslt.mm"
include "sylanbrc.mm"
include "ex.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "com12.mm"
include "3impia.mm"

theorem sslttr
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A <<s B /\ B <<s C /\ B =/= (/) ) -> A <<s C )

  proof
    cA
    cB
    csslt
    wbr
    #
    cB
    cC
    csslt
    wbr
    #
    cB
    c0
    wne
    #
    cA
    cC
    csslt
    wbr
    #
    @2
    @0
    @1
    wa
    #
    @3
    @2
    vy
    cv
    #
    cB
    wcel
    #
    vy
    wex
    @4
    @3
    wi
    #
    vy
    cB
    n0
    @6
    @7
    vy
    @6
    @4
    @3
    @6
    @4
    wa
    #
    cA
    cvv
    wcel
    #
    cC
    cvv
    wcel
    #
    wa
    #
    cA
    csur
    wss
    #
    cC
    csur
    wss
    #
    vx
    cv
    #
    vz
    cv
    #
    cslt
    wbr
    #
    vz
    cC
    wral
    vx
    cA
    wral
    #
    w3a
    @3
    @4
    @11
    @6
    @0
    @9
    @1
    @10
    cA
    cB
    ssltex1
    cB
    cC
    ssltex2
    anim12i
    adantl
    @8
    @12
    @13
    @17
    @0
    @12
    @6
    @1
    cA
    cB
    ssltss1
    ad2antrl
    #
    @1
    @13
    @6
    @0
    cB
    cC
    ssltss2
    ad2antll
    #
    @8
    @16
    vx
    vz
    cA
    cC
    @8
    @14
    cA
    wcel
    #
    @15
    cC
    wcel
    #
    wa
    #
    wa
    #
    @14
    @5
    @15
    @23
    cA
    csur
    @14
    @8
    @12
    @22
    @18
    adantr
    @8
    @20
    @21
    simprl
    #
    sseldd
    @23
    cB
    csur
    @5
    @8
    cB
    csur
    wss
    #
    @22
    @1
    @25
    @6
    @0
    cB
    cC
    ssltss1
    ad2antll
    adantr
    @6
    @4
    @22
    simpll
    #
    sseldd
    @23
    cC
    csur
    @15
    @8
    @13
    @22
    @19
    adantr
    @8
    @20
    @21
    simprr
    #
    sseldd
    @23
    @14
    @5
    cslt
    wbr
    #
    vy
    cB
    wral
    #
    @6
    @28
    @23
    @29
    vx
    cA
    wral
    #
    @20
    @29
    @8
    @30
    @22
    @0
    @30
    @6
    @1
    vx
    vy
    cA
    cB
    ssltsep
    ad2antrl
    adantr
    @24
    @29
    vx
    cA
    rsp
    sylc
    @26
    @28
    vy
    cB
    rsp
    sylc
    @23
    @5
    @15
    cslt
    wbr
    #
    vz
    cC
    wral
    #
    @21
    @31
    @23
    @32
    vy
    cB
    wral
    #
    @6
    @32
    @8
    @33
    @22
    @1
    @33
    @6
    @0
    vy
    vz
    cB
    cC
    ssltsep
    ad2antll
    adantr
    @26
    @32
    vy
    cB
    rsp
    sylc
    @27
    @31
    vz
    cC
    rsp
    sylc
    slttrd
    ralrimivva
    3jca
    vx
    vz
    cA
    cC
    brsslt
    sylanbrc
    ex
    exlimiv
    sylbi
    com12
    3impia
end
