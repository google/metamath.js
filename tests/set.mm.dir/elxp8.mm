include "cxp.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "cvv.mm"
include "wa.mm"
include "xp1st.mm"
include "wss.mm"
include "ssv.mm"
include "ssid.mm"
include "xpss12.mm"
include "mp2an.mm"
include "sseli.mm"
include "jca.mm"
include "c2nd.mm"
include "xpss.mm"
include "adantl.mm"
include "xp2nd.mm"
include "anim2i.mm"
include "elxp7.mm"
include "sylanbrc.mm"
include "impbii.mm"

theorem elxp8
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B X. C ) <-> ( ( 1st ` A ) e. B /\ A e. ( _V X. C ) ) )

  proof
    cA
    cB
    cC
    cxp
    #
    wcel
    #
    cA
    c1st
    cfv
    cB
    wcel
    #
    cA
    cvv
    cC
    cxp
    #
    wcel
    #
    wa
    #
    @1
    @2
    @4
    cA
    cB
    cC
    xp1st
    @0
    @3
    cA
    cB
    cvv
    wss
    cC
    cC
    wss
    @0
    @3
    wss
    cB
    ssv
    cC
    ssid
    cB
    cvv
    cC
    cC
    xpss12
    mp2an
    sseli
    jca
    @5
    cA
    cvv
    cvv
    cxp
    #
    wcel
    #
    @2
    cA
    c2nd
    cfv
    cC
    wcel
    #
    wa
    @1
    @4
    @7
    @2
    @3
    @6
    cA
    cvv
    cC
    xpss
    sseli
    adantl
    @4
    @8
    @2
    cA
    cvv
    cC
    xp2nd
    anim2i
    cA
    cB
    cC
    elxp7
    sylanbrc
    impbii
end
