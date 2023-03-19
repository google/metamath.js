include "ctop.mm"
include "wcel.mm"
include "ccn.mm"
include "co.mm"
include "w3a.mm"
include "crn.mm"
include "crest.mm"
include "simp3.mm"
include "cuni.mm"
include "ctopon.mm"
include "cfv.mm"
include "wss.mm"
include "wb.mm"
include "simp2.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "ssid.mm"
include "a1i.mm"
include "wf.mm"
include "cnf.mm"
include "frn.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem cnresima
  let cF: class F
  let cJ: class J
  let cK: class K


  assert |- ( ( J e. Top /\ K e. Top /\ F e. ( J Cn K ) ) -> F e. ( J Cn ( K |`t ran F ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    w3a
    #
    @2
    cF
    cJ
    cK
    cF
    crn
    #
    crest
    co
    ccn
    co
    wcel
    #
    @0
    @1
    @2
    simp3
    @3
    cK
    cK
    cuni
    #
    ctopon
    cfv
    wcel
    #
    @4
    @4
    wss
    #
    @4
    @6
    wss
    #
    @2
    @5
    wb
    @3
    @1
    @7
    @0
    @1
    @2
    simp2
    cK
    @6
    @6
    eqid
    #
    toptopon
    sylib
    @8
    @3
    @4
    ssid
    a1i
    @2
    @0
    @9
    @1
    @2
    cJ
    cuni
    #
    @6
    cF
    wf
    @9
    cF
    cJ
    cK
    @11
    @6
    @11
    eqid
    @10
    cnf
    @11
    @6
    cF
    frn
    syl
    3ad2ant3
    @4
    cF
    cJ
    cK
    @6
    cnrest2
    syl3anc
    mpbid
end
