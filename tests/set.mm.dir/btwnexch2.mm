include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wi.mm"
include "wceq.mm"
include "breq1.mm"
include "biimpd.mm"
include "adantrd.mm"
include "a1i.mm"
include "wne.mm"
include "simprl.mm"
include "simprr.mm"
include "btwnintr.mm"
include "adantr.mm"
include "mpd.mm"
include "simprrr.mm"
include "btwnouttr2.mm"
include "mp3and.mm"
include "exp32.mm"
include "pm2.61dne.mm"

theorem btwnexch2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( ( B Btwn <. A , D >. /\ C Btwn <. B , D >. ) -> C Btwn <. A , D >. ) )

  proof
    cN
    cn
    wcel
    cA
    cN
    cee
    cfv
    #
    wcel
    cB
    @0
    wcel
    wa
    cC
    @0
    wcel
    cD
    @0
    wcel
    wa
    w3a
    #
    cB
    cA
    cD
    cop
    #
    cbtwn
    wbr
    #
    cC
    cB
    cD
    cop
    cbtwn
    wbr
    #
    wa
    #
    cC
    @2
    cbtwn
    wbr
    #
    wi
    #
    cB
    cC
    cB
    cC
    wceq
    #
    @7
    wi
    @1
    @8
    @3
    @6
    @4
    @8
    @3
    @6
    cB
    cC
    @2
    cbtwn
    breq1
    biimpd
    adantrd
    a1i
    @1
    cB
    cC
    wne
    #
    @5
    @6
    @1
    @9
    @5
    wa
    #
    wa
    #
    @9
    cB
    cA
    cC
    cop
    cbtwn
    wbr
    #
    @4
    @6
    @1
    @9
    @5
    simprl
    @11
    @5
    @12
    @1
    @9
    @5
    simprr
    @1
    @5
    @12
    wi
    @10
    cA
    cB
    cC
    cD
    cN
    btwnintr
    adantr
    mpd
    @1
    @9
    @3
    @4
    simprrr
    @1
    @9
    @12
    @4
    w3a
    @6
    wi
    @10
    cA
    cB
    cC
    cD
    cN
    btwnouttr2
    adantr
    mp3and
    exp32
    pm2.61dne
end
