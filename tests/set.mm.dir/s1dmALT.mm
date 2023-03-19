include "wcel.mm"
include "cs1.mm"
include "cdm.mm"
include "cc0.mm"
include "cop.mm"
include "csn.mm"
include "s1val.mm"
include "dmeqd.mm"
include "dmsnopg.mm"
include "eqtrd.mm"

theorem s1dmALT
  let cA: class A
  let cS: class S


  assert |- ( A e. S -> dom <" A "> = { 0 } )

  proof
    cA
    cS
    wcel
    #
    cA
    cs1
    #
    cdm
    cc0
    cA
    cop
    csn
    #
    cdm
    cc0
    csn
    @0
    @1
    @2
    cA
    cS
    s1val
    dmeqd
    cc0
    cA
    cS
    dmsnopg
    eqtrd
end
