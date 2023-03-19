include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "ccnv.mm"
include "wa.mm"
include "clmim.mm"
include "wrel.mm"
include "wceq.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "eqid.mm"
include "lmhmf.mm"
include "frel.mm"
include "syl.mm"
include "dfrel2.mm"
include "sylib.mm"
include "id.mm"
include "eqeltrd.mm"
include "anim2i.mm"
include "ancoms.mm"
include "islmim2.mm"
include "3imtr4i.mm"

theorem lmimcnv
  let cS: class S
  let cT: class T
  let cF: class F


  assert |- ( F e. ( S LMIso T ) -> `' F e. ( T LMIso S ) )

  proof
    cF
    cS
    cT
    clmhm
    co
    #
    wcel
    #
    cF
    ccnv
    #
    cT
    cS
    clmhm
    co
    wcel
    #
    wa
    @3
    @2
    ccnv
    #
    @0
    wcel
    #
    wa
    #
    cF
    cS
    cT
    clmim
    co
    wcel
    @2
    cT
    cS
    clmim
    co
    wcel
    @3
    @1
    @6
    @1
    @5
    @3
    @1
    @4
    cF
    @0
    @1
    cF
    wrel
    #
    @4
    cF
    wceq
    @1
    cS
    cbs
    cfv
    #
    cT
    cbs
    cfv
    #
    cF
    wf
    @7
    @8
    @9
    cS
    cT
    cF
    @8
    eqid
    @9
    eqid
    lmhmf
    @8
    @9
    cF
    frel
    syl
    cF
    dfrel2
    sylib
    @1
    id
    eqeltrd
    anim2i
    ancoms
    cS
    cT
    cF
    islmim2
    cT
    cS
    @2
    islmim2
    3imtr4i
end
