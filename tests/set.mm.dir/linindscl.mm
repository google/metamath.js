include "clininds.mm"
include "wbr.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "wcel.mm"
include "cv.mm"
include "csca.mm"
include "c0g.mm"
include "cfsupp.mm"
include "clinc.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wi.mm"
include "cmap.mm"
include "eqid.mm"
include "linindsi.mm"
include "simpld.mm"

theorem linindscl
  let cS: class S
  let cM: class M
  let vx: setvar x
  let vf: setvar f
  let vk: setvar k


  assert |- ( S linIndS M -> S e. ~P ( Base ` M ) )

  proof
    cS
    cM
    clininds
    wbr
    cS
    cM
    cbs
    cfv
    #
    cpw
    wcel
    vf
    cv
    #
    cM
    csca
    cfv
    #
    c0g
    cfv
    #
    cfsupp
    wbr
    @1
    cS
    cM
    clinc
    cfv
    co
    cM
    c0g
    cfv
    #
    wceq
    wa
    vx
    cv
    @1
    cfv
    @3
    wceq
    vx
    cS
    wral
    wi
    vf
    @2
    cbs
    cfv
    #
    cS
    cmap
    co
    wral
    vx
    @0
    @2
    cS
    vf
    @5
    cM
    @3
    @4
    @0
    eqid
    @4
    eqid
    @2
    eqid
    @5
    eqid
    @3
    eqid
    linindsi
    simpld
end
