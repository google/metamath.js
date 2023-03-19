include "cconn.mm"
include "wcel.mm"
include "ctop.mm"
include "ccld.mm"
include "cfv.mm"
include "cin.mm"
include "c0.mm"
include "cpr.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "isconn.mm"
include "0opn.mm"
include "0cld.mm"
include "elind.mm"
include "topopn.mm"
include "topcld.mm"
include "prssi.mm"
include "syl2anc.mm"
include "biantrud.mm"
include "eqss.mm"
include "syl6rbbr.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isconn2
  let cJ: class J
  let cX: class X
  let vj: setvar j
  assume isconn.1: |- X = U. J


  assert |- ( J e. Conn <-> ( J e. Top /\ ( J i^i ( Clsd ` J ) ) C_ { (/) , X } ) )

  proof
    cJ
    cconn
    wcel
    cJ
    ctop
    wcel
    #
    cJ
    cJ
    ccld
    cfv
    #
    cin
    #
    c0
    cX
    cpr
    #
    wceq
    #
    wa
    @0
    @2
    @3
    wss
    #
    wa
    cJ
    cX
    isconn.1
    isconn
    @0
    @4
    @5
    @0
    @5
    @5
    @3
    @2
    wss
    #
    wa
    @4
    @0
    @6
    @5
    @0
    c0
    @2
    wcel
    cX
    @2
    wcel
    @6
    @0
    cJ
    @1
    c0
    cJ
    0opn
    cJ
    0cld
    elind
    @0
    cJ
    @1
    cX
    cJ
    cX
    isconn.1
    topopn
    cJ
    cX
    isconn.1
    topcld
    elind
    c0
    cX
    @2
    prssi
    syl2anc
    biantrud
    @2
    @3
    eqss
    syl6rbbr
    pm5.32i
    bitri
end
