include "crngo.mm"
include "wcel.mm"
include "crn.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "eqid.mm"
include "rngosm.mm"
include "cablo.mm"
include "w3a.mm"
include "rngoi.mm"
include "simprrd.mm"
include "rngmgmbs4.mm"
include "syl2anc.mm"
include "eqcomd.mm"

theorem rngorn1eq
  let cR: class R
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume rnplrnml0.1: |- H = ( 2nd ` R )
  assume rnplrnml0.2: |- G = ( 1st ` R )


  assert |- ( R e. RingOps -> ran G = ran H )

  proof
    cR
    crngo
    wcel
    #
    cH
    crn
    #
    cG
    crn
    #
    @0
    @2
    @2
    cxp
    @2
    cH
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    @5
    wceq
    @5
    @4
    cH
    co
    @5
    wceq
    wa
    vy
    @2
    wral
    vx
    @2
    wrex
    #
    @1
    @2
    wceq
    cR
    cG
    cH
    @2
    rnplrnml0.2
    rnplrnml0.1
    @2
    eqid
    #
    rngosm
    @0
    cG
    cablo
    wcel
    @3
    wa
    @6
    vz
    cv
    #
    cH
    co
    @4
    @5
    @9
    cH
    co
    #
    cH
    co
    wceq
    @4
    @5
    @9
    cG
    co
    cH
    co
    @6
    @4
    @9
    cH
    co
    #
    cG
    co
    wceq
    @4
    @5
    cG
    co
    @9
    cH
    co
    @11
    @10
    cG
    co
    wceq
    w3a
    vz
    @2
    wral
    vy
    @2
    wral
    vx
    @2
    wral
    @7
    vx
    vy
    vz
    cR
    cG
    cH
    @2
    rnplrnml0.2
    rnplrnml0.1
    @8
    rngoi
    simprrd
    vy
    vx
    cH
    @2
    rngmgmbs4
    syl2anc
    eqcomd
end
