include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "wne.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wo.mm"
include "btwnconn1.mm"
include "wi.mm"
include "simpr2.mm"
include "anim1i.mm"
include "btwnexch3.mm"
include "ad2antrr.mm"
include "mpd.mm"
include "ex.mm"
include "simpr3.mm"
include "simp3r.mm"
include "simp3l.mm"
include "jca.mm"
include "syld3an3.mm"
include "adantr.mm"
include "mpand.mm"
include "orim12d.mm"
include "mpdd.mm"

theorem btwnconn2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( ( A =/= B /\ B Btwn <. A , C >. /\ B Btwn <. A , D >. ) -> ( C Btwn <. B , D >. \/ D Btwn <. B , C >. ) ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    cB
    @1
    wcel
    wa
    #
    cC
    @1
    wcel
    #
    cD
    @1
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cB
    wne
    #
    cB
    cA
    cC
    cop
    #
    cbtwn
    wbr
    #
    cB
    cA
    cD
    cop
    #
    cbtwn
    wbr
    #
    w3a
    #
    cC
    @10
    cbtwn
    wbr
    #
    cD
    @8
    cbtwn
    wbr
    #
    wo
    #
    cC
    cB
    cD
    cop
    cbtwn
    wbr
    #
    cD
    cB
    cC
    cop
    cbtwn
    wbr
    #
    wo
    #
    cA
    cB
    cC
    cD
    cN
    btwnconn1
    @6
    @12
    @15
    @18
    wi
    @6
    @12
    wa
    #
    @13
    @16
    @14
    @17
    @19
    @13
    @16
    @19
    @13
    wa
    @9
    @13
    wa
    #
    @16
    @19
    @9
    @13
    @6
    @7
    @9
    @11
    simpr2
    anim1i
    @6
    @20
    @16
    wi
    @12
    @13
    cA
    cB
    cC
    cD
    cN
    btwnexch3
    ad2antrr
    mpd
    ex
    @19
    @11
    @14
    @17
    @6
    @7
    @9
    @11
    simpr3
    @6
    @11
    @14
    wa
    @17
    wi
    #
    @12
    @0
    @2
    @5
    @4
    @3
    wa
    @21
    @6
    @4
    @3
    @0
    @2
    @3
    @4
    simp3r
    @0
    @2
    @3
    @4
    simp3l
    jca
    cA
    cB
    cD
    cC
    cN
    btwnexch3
    syld3an3
    adantr
    mpand
    orim12d
    ex
    mpdd
end
