include "cr.mm"
include "wss.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "w3a.mm"
include "cun.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "clt.mm"
include "cxr.mm"
include "wcel.mm"
include "wb.mm"
include "ovolcl.mm"
include "3ad2ant1.mm"
include "simp1.mm"
include "simp2.mm"
include "unssd.mm"
include "syl.mm"
include "xrltnle.mm"
include "syl2anc.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "adantr.mm"
include "cmnf.mm"
include "mnfxr.mm"
include "a1i.mm"
include "ovolge0.mm"
include "ge0gtmnf.mm"
include "simpr.mm"
include "xrre2.mm"
include "syl32anc.mm"
include "simpl3.mm"
include "0re.mm"
include "syl6eqel.mm"
include "ovolun.mm"
include "syl22anc.mm"
include "oveq2d.mm"
include "recnd.mm"
include "addid1d.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "ex.mm"
include "sylbird.mm"
include "pm2.18d.mm"
include "ssun1.mm"
include "ovolss.mm"
include "sylancr.mm"
include "xrletri3.mm"
include "mpbir2and.mm"

theorem ovolunnul
  let cA: class A
  let cB: class B


  assert |- ( ( A C_ RR /\ B C_ RR /\ ( vol* ` B ) = 0 ) -> ( vol* ` ( A u. B ) ) = ( vol* ` A ) )

  proof
    cA
    cr
    wss
    #
    cB
    cr
    wss
    #
    cB
    covol
    cfv
    #
    cc0
    wceq
    #
    w3a
    #
    cA
    cB
    cun
    #
    covol
    cfv
    #
    cA
    covol
    cfv
    #
    wceq
    #
    @6
    @7
    cle
    wbr
    #
    @7
    @6
    cle
    wbr
    #
    @4
    @9
    @4
    @9
    wn
    #
    @7
    @6
    clt
    wbr
    #
    @9
    @4
    @7
    cxr
    wcel
    #
    @6
    cxr
    wcel
    #
    @12
    @11
    wb
    @0
    @1
    @13
    @3
    cA
    ovolcl
    #
    3ad2ant1
    #
    @4
    @5
    cr
    wss
    #
    @14
    @4
    cA
    cB
    cr
    @0
    @1
    @3
    simp1
    #
    @0
    @1
    @3
    simp2
    #
    unssd
    #
    @5
    ovolcl
    syl
    #
    @7
    @6
    xrltnle
    syl2anc
    @4
    @12
    @9
    @4
    @12
    wa
    #
    @6
    @7
    @2
    caddc
    co
    #
    @7
    cle
    @22
    @0
    @7
    cr
    wcel
    #
    @1
    @2
    cr
    wcel
    @6
    @23
    cle
    wbr
    @4
    @0
    @12
    @18
    adantr
    #
    @22
    cmnf
    cxr
    wcel
    #
    @13
    @14
    cmnf
    @7
    clt
    wbr
    #
    @12
    @24
    @26
    @22
    mnfxr
    a1i
    @22
    @0
    @13
    @25
    @15
    syl
    @4
    @14
    @12
    @21
    adantr
    @4
    @27
    @12
    @4
    @13
    cc0
    @7
    cle
    wbr
    #
    @27
    @16
    @0
    @1
    @28
    @3
    cA
    ovolge0
    3ad2ant1
    @7
    ge0gtmnf
    syl2anc
    adantr
    @4
    @12
    simpr
    cmnf
    @7
    @6
    xrre2
    syl32anc
    #
    @4
    @1
    @12
    @19
    adantr
    @22
    @2
    cc0
    cr
    @0
    @1
    @3
    @12
    simpl3
    #
    0re
    syl6eqel
    cA
    cB
    ovolun
    syl22anc
    @22
    @23
    @7
    cc0
    caddc
    co
    @7
    @22
    @2
    cc0
    @7
    caddc
    @30
    oveq2d
    @22
    @7
    @22
    @7
    @29
    recnd
    addid1d
    eqtrd
    breqtrd
    ex
    sylbird
    pm2.18d
    @4
    cA
    @5
    wss
    @17
    @10
    cA
    cB
    ssun1
    @20
    cA
    @5
    ovolss
    sylancr
    @4
    @14
    @13
    @8
    @9
    @10
    wa
    wb
    @21
    @16
    @6
    @7
    xrletri3
    syl2anc
    mpbir2and
end
