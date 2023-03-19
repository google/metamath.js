include "wfun.mm"
include "cdm.mm"
include "wlim.mm"
include "crecs.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "con0.mm"
include "wrex.mm"
include "cab.mm"
include "eqid.mm"
include "tfrlem7.mm"
include "funeqi.mm"
include "mpbir.mm"
include "tfrlem16.mm"
include "wb.mm"
include "dmeqi.mm"
include "limeq.mm"
include "ax-mp.mm"
include "pm3.2i.mm"

theorem tfr1a
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume tfr.1: |- F = recs ( G )


  assert |- ( Fun F /\ Lim dom F )

  proof
    cF
    wfun
    #
    cF
    cdm
    #
    wlim
    #
    @0
    cG
    crecs
    #
    wfun
    vx
    vy
    vf
    cv
    #
    vx
    cv
    #
    wfn
    vy
    cv
    #
    @4
    cfv
    @4
    @6
    cres
    cG
    cfv
    wceq
    vy
    @5
    wral
    wa
    vx
    con0
    wrex
    vf
    cab
    #
    vf
    cG
    @7
    eqid
    #
    tfrlem7
    cF
    @3
    tfr.1
    funeqi
    mpbir
    @2
    @3
    cdm
    #
    wlim
    #
    vx
    vy
    @7
    vf
    cG
    @8
    tfrlem16
    @1
    @9
    wceq
    @2
    @10
    wb
    cF
    @3
    tfr.1
    dmeqi
    @1
    @9
    limeq
    ax-mp
    mpbir
    pm3.2i
end
