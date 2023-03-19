include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "wa.mm"
include "wfo.mm"
include "eqid.mm"
include "biantru.mm"
include "df-fo.mm"
include "bitr4i.mm"

theorem dffn4
  let cA: class A
  let cF: class F


  assert |- ( F Fn A <-> F : A -onto-> ran F )

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
    wceq
    #
    wa
    cA
    @1
    cF
    wfo
    @2
    @0
    @1
    eqid
    biantru
    cA
    @1
    cF
    df-fo
    bitr4i
end
