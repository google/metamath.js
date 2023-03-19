include "czrh.mm"
include "cfv.mm"
include "zring.mm"
include "crh.mm"
include "co.mm"
include "cuni.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "oveq2.mm"
include "unieqd.mm"
include "df-zrh.mm"
include "ovex.mm"
include "uniex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "crg.mm"
include "cghm.mm"
include "cmgp.mm"
include "cmhm.mm"
include "cin.mm"
include "dfrhm2.mm"
include "reldmmpt2.mm"
include "ovprc2.mm"
include "uni0.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem zrhval
  let cR: class R
  let cL: class L
  let vr: setvar r
  let vs: setvar s
  let cN: class N
  let vn: setvar n
  let c.1: class .1.
  let c.x: class .x.
  assume zrhval.l: |- L = ( ZRHom ` R )


  assert |- L = U. ( ZZring RingHom R )

  proof
    cL
    cR
    czrh
    cfv
    #
    zring
    cR
    crh
    co
    #
    cuni
    #
    zrhval.l
    cR
    cvv
    wcel
    #
    @0
    @2
    wceq
    vr
    cR
    zring
    vr
    cv
    #
    crh
    co
    #
    cuni
    @2
    cvv
    czrh
    @4
    cR
    wceq
    @5
    @1
    @4
    cR
    zring
    crh
    oveq2
    unieqd
    vr
    df-zrh
    @1
    zring
    cR
    crh
    ovex
    uniex
    fvmpt
    @3
    wn
    #
    @0
    c0
    @2
    cR
    czrh
    fvprc
    @6
    @2
    c0
    cuni
    c0
    @6
    @1
    c0
    zring
    cR
    crh
    vr
    vs
    crg
    crg
    @4
    vs
    cv
    #
    cghm
    co
    @4
    cmgp
    cfv
    @7
    cmgp
    cfv
    cmhm
    co
    cin
    crh
    vs
    vr
    dfrhm2
    reldmmpt2
    ovprc2
    unieqd
    uni0
    syl6eq
    eqtr4d
    pm2.61i
    eqtri
end
