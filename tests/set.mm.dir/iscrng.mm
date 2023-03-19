include "cv.mm"
include "cmgp.mm"
include "cfv.mm"
include "ccmn.mm"
include "wcel.mm"
include "crg.mm"
include "ccrg.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "df-cring.mm"
include "elrab2.mm"

theorem iscrng
  let cR: class R
  let cG: class G
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ringmgp.g: |- G = ( mulGrp ` R )


  assert |- ( R e. CRing <-> ( R e. Ring /\ G e. CMnd ) )

  proof
    vr
    cv
    #
    cmgp
    cfv
    #
    ccmn
    wcel
    cG
    ccmn
    wcel
    vr
    cR
    crg
    ccrg
    @0
    cR
    wceq
    #
    @1
    cG
    ccmn
    @2
    @1
    cR
    cmgp
    cfv
    cG
    @0
    cR
    cmgp
    fveq2
    ringmgp.g
    syl6eqr
    eleq1d
    vr
    df-cring
    elrab2
end
