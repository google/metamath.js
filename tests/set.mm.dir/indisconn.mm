include "c0.mm"
include "cpr.mm"
include "cconn.mm"
include "wcel.mm"
include "ctop.mm"
include "ccld.mm"
include "cfv.mm"
include "cin.mm"
include "cid.mm"
include "wss.mm"
include "indistop.mm"
include "inss1.mm"
include "indislem.mm"
include "sseqtr4i.mm"
include "indisuni.mm"
include "isconn2.mm"
include "mpbir2an.mm"

theorem indisconn
  let cA: class A


  assert |- { (/) , A } e. Conn

  proof
    c0
    cA
    cpr
    #
    cconn
    wcel
    @0
    ctop
    wcel
    @0
    @0
    ccld
    cfv
    #
    cin
    #
    c0
    cA
    cid
    cfv
    #
    cpr
    #
    wss
    cA
    indistop
    @2
    @0
    @4
    @0
    @1
    inss1
    cA
    indislem
    sseqtr4i
    @0
    @3
    cA
    indisuni
    isconn2
    mpbir2an
end
