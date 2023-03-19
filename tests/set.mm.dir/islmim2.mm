include "clmim.mm"
include "co.mm"
include "wcel.mm"
include "clmhm.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "wa.mm"
include "ccnv.mm"
include "eqid.mm"
include "islmim.mm"
include "lmhmf1o.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem islmim2
  let cR: class R
  let cS: class S
  let cF: class F


  assert |- ( F e. ( R LMIso S ) <-> ( F e. ( R LMHom S ) /\ `' F e. ( S LMHom R ) ) )

  proof
    cF
    cR
    cS
    clmim
    co
    wcel
    cF
    cR
    cS
    clmhm
    co
    wcel
    #
    cR
    cbs
    cfv
    #
    cS
    cbs
    cfv
    #
    cF
    wf1o
    #
    wa
    @0
    cF
    ccnv
    cS
    cR
    clmhm
    co
    wcel
    #
    wa
    @1
    @2
    cR
    cS
    cF
    @1
    eqid
    #
    @2
    eqid
    #
    islmim
    @0
    @3
    @4
    cR
    cS
    cF
    @1
    @2
    @5
    @6
    lmhmf1o
    pm5.32i
    bitri
end
