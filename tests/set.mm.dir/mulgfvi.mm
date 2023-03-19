include "cmg.mm"
include "cfv.mm"
include "cid.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvi.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "wfn.mm"
include "cz.mm"
include "cxp.mm"
include "base0.mm"
include "eqid.mm"
include "mulgfn.mm"
include "xp0.mm"
include "fneq2i.mm"
include "mpbi.mm"
include "fn0.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem mulgfvi
  let c.x: class .x.
  let cG: class G
  assume mulgfvi.t: |- .x. = ( .g ` G )


  assert |- .x. = ( .g ` ( _I ` G ) )

  proof
    c.x
    cG
    cmg
    cfv
    #
    cG
    cid
    cfv
    #
    cmg
    cfv
    #
    mulgfvi.t
    cG
    cvv
    wcel
    #
    @0
    @2
    wceq
    @3
    cG
    @1
    cmg
    @3
    @1
    cG
    cG
    cvv
    fvi
    eqcomd
    fveq2d
    @3
    wn
    #
    @0
    c0
    @2
    cG
    cmg
    fvprc
    @4
    @2
    c0
    cmg
    cfv
    #
    c0
    @4
    @1
    c0
    cmg
    cG
    cid
    fvprc
    fveq2d
    @5
    c0
    wfn
    #
    @5
    c0
    wceq
    @5
    cz
    c0
    cxp
    #
    wfn
    @6
    c0
    @5
    c0
    base0
    @5
    eqid
    mulgfn
    @7
    c0
    @5
    cz
    xp0
    fneq2i
    mpbi
    @5
    fn0
    mpbi
    syl6eq
    eqtr4d
    pm2.61i
    eqtri
end
