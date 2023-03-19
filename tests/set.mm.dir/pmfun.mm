include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "wfun.mm"
include "elpmi.mm"
include "ffun.mm"
include "adantr.mm"
include "syl.mm"

theorem pmfun
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F e. ( A ^pm B ) -> Fun F )

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
    #
    @0
    cB
    wss
    #
    wa
    cF
    wfun
    #
    cA
    cB
    cF
    elpmi
    @1
    @3
    @2
    @0
    cA
    cF
    ffun
    adantr
    syl
end
