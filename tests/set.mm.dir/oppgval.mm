include "coppg.mm"
include "cfv.mm"
include "cnx.mm"
include "cplusg.mm"
include "ctpos.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "id.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "tposeqd.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "df-oppg.mm"
include "ovex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "reldmsets.mm"
include "ovprc1.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem oppgval
  let c.pl: class .+
  let cR: class R
  let cO: class O
  let vx: setvar x
  let cX: class X
  let cY: class Y
  assume oppgval.2: |- .+ = ( +g ` R )
  assume oppgval.3: |- O = ( oppG ` R )


  assert |- O = ( R sSet <. ( +g ` ndx ) , tpos .+ >. )

  proof
    cO
    cR
    coppg
    cfv
    #
    cR
    cnx
    cplusg
    cfv
    #
    c.pl
    ctpos
    #
    cop
    #
    csts
    co
    #
    oppgval.3
    cR
    cvv
    wcel
    #
    @0
    @4
    wceq
    vx
    cR
    vx
    cv
    #
    @1
    @6
    cplusg
    cfv
    #
    ctpos
    #
    cop
    #
    csts
    co
    @4
    cvv
    coppg
    @6
    cR
    wceq
    #
    @6
    cR
    @9
    @3
    csts
    @10
    id
    @10
    @8
    @2
    @1
    @10
    @7
    c.pl
    @10
    @7
    cR
    cplusg
    cfv
    c.pl
    @6
    cR
    cplusg
    fveq2
    oppgval.2
    syl6eqr
    tposeqd
    opeq2d
    oveq12d
    vx
    df-oppg
    cR
    @3
    csts
    ovex
    fvmpt
    @5
    wn
    @0
    c0
    @4
    cR
    coppg
    fvprc
    cR
    @3
    csts
    reldmsets
    ovprc1
    eqtr4d
    pm2.61i
    eqtri
end
