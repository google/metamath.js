include "cr.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "cc.mm"
include "ccncf.mm"
include "w3a.mm"
include "cmbf.mm"
include "cdm.mm"
include "cvol.mm"
include "cfv.mm"
include "cv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cibl.mm"
include "iccmbl.mm"
include "cnmbf.mm"
include "stoic3.mm"
include "wf.mm"
include "wceq.mm"
include "simp3.mm"
include "cncff.mm"
include "fdm.mm"
include "3syl.mm"
include "fveq2d.mm"
include "iccvolcl.mm"
include "3adant3.mm"
include "eqeltrd.mm"
include "cniccbdd.mm"
include "raleqdv.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "bddiblnc.mm"
include "syl3anc.mm"

theorem cnicciblnc
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. RR /\ B e. RR /\ F e. ( ( A [,] B ) -cn-> CC ) ) -> F e. L^1 )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cF
    cA
    cB
    cicc
    co
    #
    cc
    ccncf
    co
    wcel
    #
    w3a
    #
    cF
    cmbf
    wcel
    #
    cF
    cdm
    #
    cvol
    cfv
    #
    cr
    wcel
    vy
    cv
    cF
    cfv
    cabs
    cfv
    vx
    cv
    cle
    wbr
    #
    vy
    @6
    wral
    #
    vx
    cr
    wrex
    #
    cF
    cibl
    wcel
    @0
    @1
    @2
    cvol
    cdm
    wcel
    @3
    @5
    cA
    cB
    iccmbl
    @2
    cF
    cnmbf
    stoic3
    @4
    @7
    @2
    cvol
    cfv
    #
    cr
    @4
    @6
    @2
    cvol
    @4
    @3
    @2
    cc
    cF
    wf
    @6
    @2
    wceq
    @0
    @1
    @3
    simp3
    @2
    cc
    cF
    cncff
    @2
    cc
    cF
    fdm
    3syl
    #
    fveq2d
    @0
    @1
    @11
    cr
    wcel
    @3
    cA
    cB
    iccvolcl
    3adant3
    eqeltrd
    @4
    @10
    @8
    vy
    @2
    wral
    #
    vx
    cr
    wrex
    vx
    vy
    cA
    cB
    cF
    cniccbdd
    @4
    @9
    @13
    vx
    cr
    @4
    @8
    vy
    @6
    @2
    @12
    raleqdv
    rexbidv
    mpbird
    vx
    vy
    cF
    bddiblnc
    syl3anc
end
