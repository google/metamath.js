include "cdm.mm"
include "crn.mm"
include "wceq.mm"
include "wss.mm"
include "ccom.mm"
include "eqimss2.mm"
include "dmcosseq.mm"
include "syl.mm"

theorem dmcoeq
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( dom A = ran B -> dom ( A o. B ) = dom B )

  proof
    cA
    cdm
    #
    cB
    crn
    #
    wceq
    @1
    @0
    wss
    cA
    cB
    ccom
    cdm
    cB
    cdm
    wceq
    @1
    @0
    eqimss2
    cA
    cB
    dmcosseq
    syl
end
