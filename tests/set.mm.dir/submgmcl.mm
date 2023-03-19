include "csubmgm.mm"
include "cfv.mm"
include "wcel.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "cbs.mm"
include "wss.mm"
include "cmgm.mm"
include "wb.mm"
include "submgmrcl.mm"
include "eqid.mm"
include "issubmgm.mm"
include "syl.mm"
include "ibi.mm"
include "simprd.mm"
include "ovrspc2v.mm"
include "sylan2.mm"
include "ancoms.mm"
include "3impb.mm"

theorem submgmcl
  let c.pl: class .+
  let cS: class S
  let cM: class M
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume submgmcl.p: |- .+ = ( +g ` M )


  assert |- ( ( S e. ( SubMgm ` M ) /\ X e. S /\ Y e. S ) -> ( X .+ Y ) e. S )

  proof
    cS
    cM
    csubmgm
    cfv
    wcel
    #
    cX
    cS
    wcel
    #
    cY
    cS
    wcel
    #
    cX
    cY
    c.pl
    co
    cS
    wcel
    #
    @1
    @2
    wa
    #
    @0
    @3
    @0
    @4
    vx
    cv
    vy
    cv
    c.pl
    co
    cS
    wcel
    vy
    cS
    wral
    vx
    cS
    wral
    #
    @3
    @0
    cS
    cM
    cbs
    cfv
    #
    wss
    #
    @5
    @0
    @7
    @5
    wa
    #
    @0
    cM
    cmgm
    wcel
    @0
    @8
    wb
    cS
    cM
    submgmrcl
    vx
    vy
    @6
    c.pl
    cS
    cM
    @6
    eqid
    submgmcl.p
    issubmgm
    syl
    ibi
    simprd
    vx
    vy
    cS
    cS
    cS
    c.pl
    cX
    cY
    ovrspc2v
    sylan2
    ancoms
    3impb
end
