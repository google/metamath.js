include "cgim.mm"
include "co.mm"
include "wcel.mm"
include "cghm.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "wa.mm"
include "ccnv.mm"
include "eqid.mm"
include "isgim.mm"
include "ghmf1o.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isgim2
  let cR: class R
  let cS: class S
  let cF: class F


  assert |- ( F e. ( R GrpIso S ) <-> ( F e. ( R GrpHom S ) /\ `' F e. ( S GrpHom R ) ) )

  proof
    cF
    cR
    cS
    cgim
    co
    wcel
    cF
    cR
    cS
    cghm
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
    cghm
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
    isgim
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
    ghmf1o
    pm5.32i
    bitri
end
