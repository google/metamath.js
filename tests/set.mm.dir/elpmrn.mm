include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cdm.mm"
include "wf.mm"
include "crn.mm"
include "wss.mm"
include "elpmi.mm"
include "simpld.mm"
include "frn.mm"
include "syl.mm"

theorem elpmrn
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F e. ( A ^pm B ) -> ran F C_ A )

  proof
    cF
    cA
    cB
    cpm
    co
    wcel
    #
    cF
    cdm
    #
    cA
    cF
    wf
    #
    cF
    crn
    cA
    wss
    @0
    @2
    @1
    cB
    wss
    cA
    cB
    cF
    elpmi
    simpld
    @1
    cA
    cF
    frn
    syl
end
