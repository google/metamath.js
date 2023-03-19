include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "wo.mm"
include "w3a.mm"
include "cdom.mm"
include "wbr.mm"
include "wn.mm"
include "csdm.mm"
include "wa.mm"
include "wpss.mm"
include "simpl1.mm"
include "simpr.mm"
include "simpl3.mm"
include "orel1.mm"
include "sylc.mm"
include "dfpss3.mm"
include "sylanbrc.mm"
include "php3.mm"
include "syl2anc.mm"
include "ex.mm"
include "domnsym.mm"
include "con2i.mm"
include "syl6.mm"
include "con4d.mm"
include "wi.mm"
include "ssdomg.mm"
include "3ad2ant2.mm"
include "impbid.mm"

theorem fincssdom
  let cA: class A
  let cB: class B


  assert |- ( ( A e. Fin /\ B e. Fin /\ ( A C_ B \/ B C_ A ) ) -> ( A ~<_ B <-> A C_ B ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wo
    #
    w3a
    #
    cA
    cB
    cdom
    wbr
    #
    @2
    @5
    @2
    @6
    @5
    @2
    wn
    #
    cB
    cA
    csdm
    wbr
    #
    @6
    wn
    @5
    @7
    @8
    @5
    @7
    wa
    #
    @0
    cB
    cA
    wpss
    #
    @8
    @0
    @1
    @4
    @7
    simpl1
    @9
    @3
    @7
    @10
    @9
    @7
    @4
    @3
    @5
    @7
    simpr
    #
    @0
    @1
    @4
    @7
    simpl3
    @2
    @3
    orel1
    sylc
    @11
    cB
    cA
    dfpss3
    sylanbrc
    cA
    cB
    php3
    syl2anc
    ex
    @6
    @8
    cA
    cB
    domnsym
    con2i
    syl6
    con4d
    @1
    @0
    @2
    @6
    wi
    @4
    cA
    cB
    cfn
    ssdomg
    3ad2ant2
    impbid
end
