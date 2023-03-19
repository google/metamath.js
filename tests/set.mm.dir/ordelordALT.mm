include "word.mm"
include "wcel.mm"
include "wa.mm"
include "wtr.mm"
include "wel.mm"
include "weq.mm"
include "w3o.mm"
include "wral.mm"
include "ordtr.mm"
include "adantr.mm"
include "dford2.mm"
include "simprbi.mm"
include "3orcomb.mm"
include "2ralbii.mm"
include "sylib.mm"
include "simpr.mm"
include "tratrb.mm"
include "syl3anc.mm"
include "wss.mm"
include "trss.mm"
include "sylc.mm"
include "wi.mm"
include "ssralv2.mm"
include "ex.mm"
include "syl3c.mm"
include "sylanbrc.mm"

theorem ordelordALT
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( Ord A /\ B e. A ) -> Ord B )

  proof
    cA
    word
    #
    cB
    cA
    wcel
    #
    wa
    #
    cB
    wtr
    #
    vx
    vy
    wel
    #
    vx
    vy
    weq
    #
    vy
    vx
    wel
    #
    w3o
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    cB
    word
    @2
    cA
    wtr
    #
    @4
    @6
    @5
    w3o
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @1
    @3
    @0
    @9
    @1
    cA
    ordtr
    adantr
    #
    @2
    @7
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @11
    @0
    @13
    @1
    @0
    @9
    @13
    vx
    vy
    cA
    dford2
    simprbi
    adantr
    #
    @7
    @10
    vx
    vy
    cA
    cA
    @4
    @5
    @6
    3orcomb
    2ralbii
    sylib
    @0
    @1
    simpr
    #
    vx
    vy
    cA
    cB
    tratrb
    syl3anc
    @2
    cB
    cA
    wss
    #
    @16
    @13
    @8
    @2
    @9
    @1
    @16
    @12
    @15
    cA
    cB
    trss
    sylc
    #
    @17
    @14
    @16
    @16
    @13
    @8
    wi
    @7
    vx
    vy
    cB
    cA
    cB
    cA
    ssralv2
    ex
    syl3c
    vx
    vy
    cB
    dford2
    sylanbrc
end
