include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "ccnv.mm"
include "wa.mm"
include "cgim.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "wceq.mm"
include "eqid.mm"
include "ghmf.mm"
include "wrel.mm"
include "frel.mm"
include "dfrel2.mm"
include "sylib.mm"
include "syl.mm"
include "id.mm"
include "eqeltrd.mm"
include "anim2i.mm"
include "ancoms.mm"
include "isgim2.mm"
include "3imtr4i.mm"

theorem gimcnv
  let cS: class S
  let cT: class T
  let cF: class F


  assert |- ( F e. ( S GrpIso T ) -> `' F e. ( T GrpIso S ) )

  proof
    cF
    cS
    cT
    cghm
    co
    #
    wcel
    #
    cF
    ccnv
    #
    cT
    cS
    cghm
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
    cgim
    co
    wcel
    @2
    cT
    cS
    cgim
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
    #
    @4
    cF
    wceq
    #
    cS
    cT
    cF
    @7
    @8
    @7
    eqid
    @8
    eqid
    ghmf
    @9
    cF
    wrel
    @10
    @7
    @8
    cF
    frel
    cF
    dfrel2
    sylib
    syl
    @1
    id
    eqeltrd
    anim2i
    ancoms
    cS
    cT
    cF
    isgim2
    cT
    cS
    @2
    isgim2
    3imtr4i
end
