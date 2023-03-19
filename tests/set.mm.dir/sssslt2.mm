include "csslt.mm"
include "wbr.mm"
include "wss.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "csur.mm"
include "cv.mm"
include "cslt.mm"
include "wral.mm"
include "w3a.mm"
include "ssltex1.mm"
include "adantr.mm"
include "ssltex2.mm"
include "simpr.mm"
include "ssexd.mm"
include "jca.mm"
include "ssltss1.mm"
include "ssltss2.mm"
include "sstrd.mm"
include "ssltsep.mm"
include "wi.mm"
include "ssralv.mm"
include "syl.mm"
include "ralimdv.mm"
include "mpd.mm"
include "3jca.mm"
include "brsslt.mm"
include "sylanbrc.mm"

theorem sssslt2
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A <<s B /\ C C_ B ) -> A <<s C )

  proof
    cA
    cB
    csslt
    wbr
    #
    cC
    cB
    wss
    #
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
    vy
    cv
    cslt
    wbr
    #
    vy
    cC
    wral
    #
    vx
    cA
    wral
    #
    w3a
    cA
    cC
    csslt
    wbr
    @2
    @3
    @4
    @0
    @3
    @1
    cA
    cB
    ssltex1
    adantr
    @2
    cC
    cB
    cvv
    @0
    cB
    cvv
    wcel
    @1
    cA
    cB
    ssltex2
    adantr
    @0
    @1
    simpr
    #
    ssexd
    jca
    @2
    @5
    @6
    @9
    @0
    @5
    @1
    cA
    cB
    ssltss1
    adantr
    @2
    cC
    cB
    csur
    @10
    @0
    cB
    csur
    wss
    @1
    cA
    cB
    ssltss2
    adantr
    sstrd
    @2
    @7
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    @9
    @0
    @12
    @1
    vx
    vy
    cA
    cB
    ssltsep
    adantr
    @2
    @11
    @8
    vx
    cA
    @2
    @1
    @11
    @8
    wi
    @10
    @7
    vy
    cC
    cB
    ssralv
    syl
    ralimdv
    mpd
    3jca
    vx
    vy
    cA
    cC
    brsslt
    sylanbrc
end
