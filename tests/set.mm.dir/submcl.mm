include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "cbs.mm"
include "wss.mm"
include "c0g.mm"
include "w3a.mm"
include "cmnd.mm"
include "wb.mm"
include "submrcl.mm"
include "eqid.mm"
include "issubm.mm"
include "syl.mm"
include "ibi.mm"
include "simp3d.mm"
include "ovrspc2v.mm"
include "sylan2.mm"
include "ancoms.mm"
include "3impb.mm"

theorem submcl
  let c.pl: class .+
  let cS: class S
  let cM: class M
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume submcl.p: |- .+ = ( +g ` M )


  assert |- ( ( S e. ( SubMnd ` M ) /\ X e. S /\ Y e. S ) -> ( X .+ Y ) e. S )

  proof
    cS
    cM
    csubmnd
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
    cM
    c0g
    cfv
    #
    cS
    wcel
    #
    @5
    @0
    @7
    @9
    @5
    w3a
    #
    @0
    cM
    cmnd
    wcel
    @0
    @10
    wb
    cS
    cM
    submrcl
    vx
    vy
    @6
    c.pl
    cS
    cM
    @8
    @6
    eqid
    @8
    eqid
    submcl.p
    issubm
    syl
    ibi
    simp3d
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
