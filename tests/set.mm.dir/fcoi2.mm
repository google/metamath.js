include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "ccom.mm"
include "wceq.mm"
include "df-f.mm"
include "cores.mm"
include "wrel.mm"
include "fnrel.mm"
include "coi2.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "sylbi.mm"

theorem fcoi2
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A --> B -> ( ( _I |` B ) o. F ) = F )

  proof
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    #
    cF
    crn
    cB
    wss
    #
    wa
    cid
    cB
    cres
    cF
    ccom
    #
    cF
    wceq
    cA
    cB
    cF
    df-f
    @1
    @0
    @2
    cid
    cF
    ccom
    #
    cF
    cid
    cF
    cB
    cores
    @0
    cF
    wrel
    @3
    cF
    wceq
    cA
    cF
    fnrel
    cF
    coi2
    syl
    sylan9eqr
    sylbi
end
