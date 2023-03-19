include "cc.mm"
include "wss.mm"
include "wa.mm"
include "ccncf.mm"
include "co.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "cfv.mm"
include "ccn.mm"
include "eqid.mm"
include "cncfmet.mm"
include "crest.mm"
include "cxmt.mm"
include "wcel.mm"
include "wceq.mm"
include "cnxmet.mm"
include "simpl.mm"
include "cnfldtopn.mm"
include "metrest.mm"
include "sylancr.mm"
include "syl5eq.mm"
include "simpr.mm"
include "oveq12d.mm"
include "eqtr4d.mm"

theorem cncfcn
  let cA: class A
  let cB: class B
  let cJ: class J
  let cK: class K
  let cL: class L
  assume cncfcn.2: |- J = ( TopOpen ` CCfld )
  assume cncfcn.3: |- K = ( J |`t A )
  assume cncfcn.4: |- L = ( J |`t B )


  assert |- ( ( A C_ CC /\ B C_ CC ) -> ( A -cn-> B ) = ( K Cn L ) )

  proof
    cA
    cc
    wss
    #
    cB
    cc
    wss
    #
    wa
    #
    cA
    cB
    ccncf
    co
    cabs
    cmin
    ccom
    #
    cA
    cA
    cxp
    cres
    #
    cmopn
    cfv
    #
    @3
    cB
    cB
    cxp
    cres
    #
    cmopn
    cfv
    #
    ccn
    co
    cK
    cL
    ccn
    co
    cA
    cB
    @4
    @6
    @5
    @7
    @4
    eqid
    #
    @6
    eqid
    #
    @5
    eqid
    #
    @7
    eqid
    #
    cncfmet
    @2
    cK
    @5
    cL
    @7
    ccn
    @2
    cK
    cJ
    cA
    crest
    co
    #
    @5
    cncfcn.3
    @2
    @3
    cc
    cxmt
    cfv
    wcel
    #
    @0
    @12
    @5
    wceq
    cnxmet
    @0
    @1
    simpl
    @3
    @4
    cJ
    @5
    cc
    cA
    @8
    cJ
    cncfcn.2
    cnfldtopn
    #
    @10
    metrest
    sylancr
    syl5eq
    @2
    cL
    cJ
    cB
    crest
    co
    #
    @7
    cncfcn.4
    @2
    @13
    @1
    @15
    @7
    wceq
    cnxmet
    @0
    @1
    simpr
    @3
    @6
    cJ
    @7
    cc
    cB
    @9
    @14
    @11
    metrest
    sylancr
    syl5eq
    oveq12d
    eqtr4d
end
