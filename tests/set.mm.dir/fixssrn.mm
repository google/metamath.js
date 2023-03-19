include "cfix.mm"
include "cid.mm"
include "cin.mm"
include "crn.mm"
include "dffix2.mm"
include "wss.mm"
include "inss1.mm"
include "rnss.mm"
include "ax-mp.mm"
include "eqsstri.mm"

theorem fixssrn
  let cA: class A


  assert |- Fix A C_ ran A

  proof
    cA
    cfix
    cA
    cid
    cin
    #
    crn
    #
    cA
    crn
    #
    cA
    dffix2
    @0
    cA
    wss
    @1
    @2
    wss
    cA
    cid
    inss1
    @0
    cA
    rnss
    ax-mp
    eqsstri
end
