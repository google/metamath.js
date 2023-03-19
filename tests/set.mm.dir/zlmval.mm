include "wcel.mm"
include "czlm.mm"
include "cfv.mm"
include "cnx.mm"
include "csca.mm"
include "zring.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvsca.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "cmg.mm"
include "oveq1.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "df-zlm.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem zlmval
  let c.x: class .x.
  let cG: class G
  let cV: class V
  let cW: class W
  let vg: setvar g
  assume zlmval.w: |- W = ( ZMod ` G )
  assume zlmval.m: |- .x. = ( .g ` G )


  assert |- ( G e. V -> W = ( ( G sSet <. ( Scalar ` ndx ) , ZZring >. ) sSet <. ( .s ` ndx ) , .x. >. ) )

  proof
    cG
    cV
    wcel
    #
    cW
    cG
    czlm
    cfv
    #
    cG
    cnx
    csca
    cfv
    zring
    cop
    #
    csts
    co
    #
    cnx
    cvsca
    cfv
    #
    c.x
    cop
    #
    csts
    co
    #
    zlmval.w
    @0
    cG
    cvv
    wcel
    @1
    @6
    wceq
    cG
    cV
    elex
    vg
    cG
    vg
    cv
    #
    @2
    csts
    co
    #
    @4
    @7
    cmg
    cfv
    #
    cop
    #
    csts
    co
    @6
    cvv
    czlm
    @7
    cG
    wceq
    #
    @8
    @3
    @10
    @5
    csts
    @7
    cG
    @2
    csts
    oveq1
    @11
    @9
    c.x
    @4
    @11
    @9
    cG
    cmg
    cfv
    c.x
    @7
    cG
    cmg
    fveq2
    zlmval.m
    syl6eqr
    opeq2d
    oveq12d
    vg
    df-zlm
    @3
    @5
    csts
    ovex
    fvmpt
    syl
    syl5eq
end
