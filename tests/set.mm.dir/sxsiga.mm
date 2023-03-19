include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "csx.mm"
include "co.mm"
include "cv.mm"
include "cxp.mm"
include "cmpt2.mm"
include "cfv.mm"
include "csigagen.mm"
include "eqid.mm"
include "sxval.mm"
include "cvv.mm"
include "txbasex.mm"
include "sigagensiga.mm"
include "syl.mm"
include "eqeltrd.mm"
include "elrnsiga.mm"

theorem sxsiga
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( S e. U. ran sigAlgebra /\ T e. U. ran sigAlgebra ) -> ( S sX T ) e. U. ran sigAlgebra )

  proof
    cS
    csiga
    crn
    cuni
    #
    wcel
    cT
    @0
    wcel
    wa
    #
    cS
    cT
    csx
    co
    #
    vx
    vy
    cS
    cT
    vx
    cv
    vy
    cv
    cxp
    cmpt2
    crn
    #
    cuni
    #
    csiga
    cfv
    #
    wcel
    @2
    @0
    wcel
    @1
    @2
    @3
    csigagen
    cfv
    #
    @5
    vx
    vy
    @3
    cS
    cT
    @0
    @0
    @3
    eqid
    #
    sxval
    @1
    @3
    cvv
    wcel
    @6
    @5
    wcel
    vx
    vy
    @3
    cS
    cT
    @0
    @0
    @7
    txbasex
    @3
    cvv
    sigagensiga
    syl
    eqeltrd
    @2
    @4
    elrnsiga
    syl
end
