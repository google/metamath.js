include "crngo.mm"
include "wcel.mm"
include "cidl.mm"
include "cfv.mm"
include "w3a.mm"
include "cpr.mm"
include "cint.mm"
include "cin.mm"
include "wceq.mm"
include "intprg.mm"
include "3adant1.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "prnzg.mm"
include "adantr.mm"
include "prssi.mm"
include "jca.mm"
include "intidl.mm"
include "3expb.mm"
include "sylan2.mm"
include "3impb.mm"
include "eqeltrrd.mm"

theorem inidl
  let cR: class R
  let cI: class I
  let cJ: class J


  assert |- ( ( R e. RingOps /\ I e. ( Idl ` R ) /\ J e. ( Idl ` R ) ) -> ( I i^i J ) e. ( Idl ` R ) )

  proof
    cR
    crngo
    wcel
    #
    cI
    cR
    cidl
    cfv
    #
    wcel
    #
    cJ
    @1
    wcel
    #
    w3a
    cI
    cJ
    cpr
    #
    cint
    #
    cI
    cJ
    cin
    #
    @1
    @2
    @3
    @5
    @6
    wceq
    @0
    cI
    cJ
    @1
    @1
    intprg
    3adant1
    @0
    @2
    @3
    @5
    @1
    wcel
    #
    @2
    @3
    wa
    #
    @0
    @4
    c0
    wne
    #
    @4
    @1
    wss
    #
    wa
    @7
    @8
    @9
    @10
    @2
    @9
    @3
    cI
    cJ
    @1
    prnzg
    adantr
    cI
    cJ
    @1
    prssi
    jca
    @0
    @9
    @10
    @7
    @4
    cR
    intidl
    3expb
    sylan2
    3impb
    eqeltrrd
end
