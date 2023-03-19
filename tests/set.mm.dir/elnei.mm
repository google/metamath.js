include "ctop.mm"
include "wcel.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "w3a.mm"
include "wss.mm"
include "ssnei.mm"
include "3adant2.mm"
include "wb.mm"
include "snssg.mm"
include "3ad2ant2.mm"
include "mpbird.mm"

theorem elnei
  let cA: class A
  let cP: class P
  let cJ: class J
  let cN: class N


  assert |- ( ( J e. Top /\ P e. A /\ N e. ( ( nei ` J ) ` { P } ) ) -> P e. N )

  proof
    cJ
    ctop
    wcel
    #
    cP
    cA
    wcel
    #
    cN
    cP
    csn
    #
    cJ
    cnei
    cfv
    cfv
    wcel
    #
    w3a
    cP
    cN
    wcel
    #
    @2
    cN
    wss
    #
    @0
    @3
    @5
    @1
    @2
    cJ
    cN
    ssnei
    3adant2
    @1
    @0
    @4
    @5
    wb
    @3
    cP
    cN
    cA
    snssg
    3ad2ant2
    mpbird
end
