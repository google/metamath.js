include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "ctop.mm"
include "cuni.mm"
include "wss.mm"
include "wb.mm"
include "cldrcl.mm"
include "eqid.mm"
include "cldss.mm"
include "restcld.mm"
include "syl2anc.mm"
include "wa.mm"
include "incld.mm"
include "ancoms.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "imp.mm"

theorem restcldr
  let cA: class A
  let cB: class B
  let cJ: class J
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  let cV: class V
  let cC: class C


  assert |- ( ( A e. ( Clsd ` J ) /\ B e. ( Clsd ` ( J |`t A ) ) ) -> B e. ( Clsd ` J ) )

  proof
    cA
    cJ
    ccld
    cfv
    #
    wcel
    #
    cB
    cJ
    cA
    crest
    co
    ccld
    cfv
    wcel
    #
    cB
    @0
    wcel
    #
    @1
    @2
    cB
    vv
    cv
    #
    cA
    cin
    #
    wceq
    #
    vv
    @0
    wrex
    #
    @3
    @1
    cJ
    ctop
    wcel
    cA
    cJ
    cuni
    #
    wss
    @2
    @7
    wb
    cA
    cJ
    cldrcl
    cA
    cJ
    @8
    @8
    eqid
    #
    cldss
    vv
    cB
    cA
    cJ
    @8
    @9
    restcld
    syl2anc
    @1
    @6
    @3
    vv
    @0
    @1
    @4
    @0
    wcel
    #
    wa
    @3
    @6
    @5
    @0
    wcel
    #
    @10
    @1
    @11
    @4
    cA
    cJ
    incld
    ancoms
    cB
    @5
    @0
    eleq1
    syl5ibrcom
    rexlimdva
    sylbid
    imp
end
