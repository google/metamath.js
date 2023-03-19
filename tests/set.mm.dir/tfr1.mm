include "con0.mm"
include "wfn.mm"
include "crecs.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "cres.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "eqid.mm"
include "tfrlem7.mm"
include "tfrlem14.mm"
include "df-fn.mm"
include "mpbir2an.mm"
include "fneq1i.mm"
include "mpbir.mm"

theorem tfr1
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume tfr.1: |- F = recs ( G )


  assert |- F Fn On

  proof
    cF
    con0
    wfn
    cG
    crecs
    #
    con0
    wfn
    #
    @1
    @0
    wfun
    @0
    cdm
    con0
    wceq
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
    @2
    cfv
    @2
    @4
    cres
    cG
    cfv
    wceq
    vy
    @3
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
    @5
    eqid
    #
    tfrlem7
    vx
    vy
    @5
    vf
    cG
    @6
    tfrlem14
    @0
    con0
    df-fn
    mpbir2an
    con0
    cF
    @0
    tfr.1
    fneq1i
    mpbir
end
