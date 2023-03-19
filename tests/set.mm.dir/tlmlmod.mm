include "ctlm.mm"
include "wcel.mm"
include "ctmd.mm"
include "clmod.mm"
include "csca.mm"
include "cfv.mm"
include "ctrg.mm"
include "w3a.mm"
include "cscaf.mm"
include "ctopn.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "eqid.mm"
include "istlm.mm"
include "simplbi.mm"
include "simp2d.mm"

theorem tlmlmod
  let cW: class W


  assert |- ( W e. TopMod -> W e. LMod )

  proof
    cW
    ctlm
    wcel
    #
    cW
    ctmd
    wcel
    #
    cW
    clmod
    wcel
    #
    cW
    csca
    cfv
    #
    ctrg
    wcel
    #
    @0
    @1
    @2
    @4
    w3a
    cW
    cscaf
    cfv
    #
    @3
    ctopn
    cfv
    #
    cW
    ctopn
    cfv
    #
    ctx
    co
    @7
    ccn
    co
    wcel
    @5
    @3
    @7
    @6
    cW
    @5
    eqid
    @7
    eqid
    @3
    eqid
    @6
    eqid
    istlm
    simplbi
    simp2d
end
