include "cinvr.mm"
include "cfv.mm"
include "cminusg.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "cmgp.mm"
include "cui.mm"
include "cress.mm"
include "co.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "df-invr.mm"
include "fvex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "wfn.mm"
include "base0.mm"
include "eqid.mm"
include "grpinvfn.mm"
include "fn0.mm"
include "mpbi.mm"
include "oveq1d.mm"
include "syl5eq.mm"
include "ress0.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem invrfval
  let cR: class R
  let cU: class U
  let cG: class G
  let cI: class I
  let vr: setvar r
  assume invrfval.u: |- U = ( Unit ` R )
  assume invrfval.g: |- G = ( ( mulGrp ` R ) |`s U )
  assume invrfval.i: |- I = ( invr ` R )


  assert |- I = ( invg ` G )

  proof
    cI
    cR
    cinvr
    cfv
    #
    cG
    cminusg
    cfv
    #
    invrfval.i
    cR
    cvv
    wcel
    #
    @0
    @1
    wceq
    vr
    cR
    vr
    cv
    #
    cmgp
    cfv
    #
    @3
    cui
    cfv
    #
    cress
    co
    #
    cminusg
    cfv
    @1
    cvv
    cinvr
    @3
    cR
    wceq
    #
    @6
    cG
    cminusg
    @7
    @6
    cR
    cmgp
    cfv
    #
    cU
    cress
    co
    #
    cG
    @7
    @4
    @8
    @5
    cU
    cress
    @3
    cR
    cmgp
    fveq2
    @7
    @5
    cR
    cui
    cfv
    cU
    @3
    cR
    cui
    fveq2
    invrfval.u
    syl6eqr
    oveq12d
    invrfval.g
    syl6eqr
    fveq2d
    vr
    df-invr
    cG
    cminusg
    fvex
    fvmpt
    @2
    wn
    #
    @0
    c0
    cminusg
    cfv
    #
    @1
    @10
    @0
    c0
    @11
    cR
    cinvr
    fvprc
    @11
    c0
    wfn
    @11
    c0
    wceq
    c0
    c0
    @11
    base0
    @11
    eqid
    grpinvfn
    @11
    fn0
    mpbi
    syl6eqr
    @10
    cG
    c0
    cminusg
    @10
    cG
    c0
    cU
    cress
    co
    #
    c0
    @10
    cG
    @9
    @12
    invrfval.g
    @10
    @8
    c0
    cU
    cress
    cR
    cmgp
    fvprc
    oveq1d
    syl5eq
    cU
    ress0
    syl6eq
    fveq2d
    eqtr4d
    pm2.61i
    eqtri
end
