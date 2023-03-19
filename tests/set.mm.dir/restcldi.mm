include "wss.mm"
include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "simp2.mm"
include "dfss.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ctop.mm"
include "wb.mm"
include "cldrcl.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "restcld.mm"
include "mpbird.mm"

theorem restcldi
  let cA: class A
  let cB: class B
  let cJ: class J
  let cX: class X
  let vv: setvar v
  assume restcldi.1: |- X = U. J


  assert |- ( ( A C_ X /\ B e. ( Clsd ` J ) /\ B C_ A ) -> B e. ( Clsd ` ( J |`t A ) ) )

  proof
    cA
    cX
    wss
    #
    cB
    cJ
    ccld
    cfv
    #
    wcel
    #
    cB
    cA
    wss
    #
    w3a
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
    vv
    cv
    #
    cA
    cin
    #
    wceq
    #
    vv
    @1
    wrex
    #
    @4
    @2
    cB
    cB
    cA
    cin
    #
    wceq
    #
    @9
    @0
    @2
    @3
    simp2
    @3
    @0
    @11
    @2
    @3
    @11
    cB
    cA
    dfss
    biimpi
    3ad2ant3
    @8
    @11
    vv
    cB
    @1
    @6
    cB
    wceq
    @7
    @10
    cB
    @6
    cB
    cA
    ineq1
    eqeq2d
    rspcev
    syl2anc
    @4
    cJ
    ctop
    wcel
    #
    @0
    @5
    @9
    wb
    @2
    @0
    @12
    @3
    cB
    cJ
    cldrcl
    3ad2ant2
    @0
    @2
    @3
    simp1
    vv
    cB
    cA
    cJ
    cX
    restcldi.1
    restcld
    syl2anc
    mpbird
end
