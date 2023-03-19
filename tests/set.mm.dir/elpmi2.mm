include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "elpmi.mm"
include "simprd.mm"

theorem elpmi2
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F e. ( A ^pm B ) -> dom F C_ B )

  proof
    cF
    cA
    cB
    cpm
    co
    wcel
    cF
    cdm
    #
    cA
    cF
    wf
    @0
    cB
    wss
    cA
    cB
    cF
    elpmi
    simprd
end
