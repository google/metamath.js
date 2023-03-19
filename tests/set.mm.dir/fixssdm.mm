include "cfix.mm"
include "cid.mm"
include "cin.mm"
include "cdm.mm"
include "df-fix.mm"
include "wss.mm"
include "inss1.mm"
include "dmss.mm"
include "ax-mp.mm"
include "eqsstri.mm"

theorem fixssdm
  let cA: class A


  assert |- Fix A C_ dom A

  proof
    cA
    cfix
    cA
    cid
    cin
    #
    cdm
    #
    cA
    cdm
    #
    cA
    df-fix
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
    dmss
    ax-mp
    eqsstri
end
