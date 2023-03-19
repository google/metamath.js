include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wa.mm"
include "wfn.mm"
include "eqid.mm"
include "biantru.mm"
include "df-fn.mm"
include "bitr4i.mm"

theorem funfn
  let cA: class A


  assert |- ( Fun A <-> A Fn dom A )

  proof
    cA
    wfun
    #
    @0
    cA
    cdm
    #
    @1
    wceq
    #
    wa
    cA
    @1
    wfn
    @2
    @0
    @1
    eqid
    biantru
    cA
    @1
    df-fn
    bitr4i
end
