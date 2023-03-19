include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "wf.mm"
include "ssid.mm"
include "biantru.mm"
include "df-f.mm"
include "bitr4i.mm"

theorem dffn3
  let cA: class A
  let cF: class F


  assert |- ( F Fn A <-> F : A --> ran F )

  proof
    cF
    cA
    wfn
    #
    @0
    cF
    crn
    #
    @1
    wss
    #
    wa
    cA
    @1
    cF
    wf
    @2
    @0
    @1
    ssid
    biantru
    cA
    @1
    cF
    df-f
    bitr4i
end
