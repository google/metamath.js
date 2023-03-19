include "wcel.mm"
include "cuni.mm"
include "cvv.mm"
include "cdm.mm"
include "uniexg.mm"
include "wss.mm"
include "crn.mm"
include "cun.mm"
include "ssun1.mm"
include "dmrnssfld.mm"
include "sstri.mm"
include "ssexg.mm"
include "mpan.mm"
include "3syl.mm"

theorem dmexg
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> dom A e. _V )

  proof
    cA
    cV
    wcel
    cA
    cuni
    #
    cvv
    wcel
    @0
    cuni
    #
    cvv
    wcel
    #
    cA
    cdm
    #
    cvv
    wcel
    #
    cA
    cV
    uniexg
    @0
    cvv
    uniexg
    @3
    @1
    wss
    @2
    @4
    @3
    @3
    cA
    crn
    #
    cun
    @1
    @3
    @5
    ssun1
    cA
    dmrnssfld
    sstri
    @3
    @1
    cvv
    ssexg
    mpan
    3syl
end
