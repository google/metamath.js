include "cur.mm"
include "cfv.mm"
include "cmgp.mm"
include "c0g.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "ccom.mm"
include "df-ur.mm"
include "fveq1i.mm"
include "wfn.mm"
include "fnmgp.mm"
include "fvco2.mm"
include "mpan.mm"
include "syl5eq.mm"
include "wn.mm"
include "c0.mm"
include "0g0.mm"
include "fvprc.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "fveq2i.mm"
include "3eqtr4i.mm"

theorem ringidval
  let cR: class R
  let c.1: class .1.
  let cG: class G
  assume ringidval.g: |- G = ( mulGrp ` R )
  assume ringidval.u: |- .1. = ( 1r ` R )


  assert |- .1. = ( 0g ` G )

  proof
    cR
    cur
    cfv
    #
    cR
    cmgp
    cfv
    #
    c0g
    cfv
    #
    c.1
    cG
    c0g
    cfv
    cR
    cvv
    wcel
    #
    @0
    @2
    wceq
    @3
    @0
    cR
    c0g
    cmgp
    ccom
    #
    cfv
    #
    @2
    cR
    cur
    @4
    df-ur
    fveq1i
    cmgp
    cvv
    wfn
    @3
    @5
    @2
    wceq
    fnmgp
    cvv
    c0g
    cmgp
    cR
    fvco2
    mpan
    syl5eq
    @3
    wn
    #
    c0
    c0
    c0g
    cfv
    @0
    @2
    0g0
    cR
    cur
    fvprc
    @6
    @1
    c0
    c0g
    cR
    cmgp
    fvprc
    fveq2d
    3eqtr4a
    pm2.61i
    ringidval.u
    cG
    @1
    c0g
    ringidval.g
    fveq2i
    3eqtr4i
end
