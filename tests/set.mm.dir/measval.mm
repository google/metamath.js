include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "wf.mm"
include "c0.mm"
include "cfv.mm"
include "wceq.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wa.mm"
include "cesum.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "w3a.mm"
include "cab.mm"
include "cvv.mm"
include "cmeas.mm"
include "wss.mm"
include "simp1.mm"
include "ss2abi.mm"
include "ovex.mm"
include "mapex.mm"
include "mpan2.mm"
include "ssexg.mm"
include "sylancr.mm"
include "feq2.mm"
include "pweq.mm"
include "raleqdv.mm"
include "3anbi13d.mm"
include "abbidv.mm"
include "df-meas.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem measval
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let vm: setvar m
  let vs: setvar s

  disjoint m x
  disjoint m y
  disjoint x y
  disjoint S m
  disjoint S x
  disjoint m s
  disjoint s x
  disjoint S s
  disjoint s y
  assert |- ( S e. U. ran sigAlgebra -> ( measures ` S ) = { m | ( m : S --> ( 0 [,] +oo ) /\ ( m ` (/) ) = 0 /\ A. x e. ~P S ( ( x ~<_ _om /\ Disj_ y e. x y ) -> ( m ` U. x ) = sum* y e. x ( m ` y ) ) ) } )

  proof
    cS
    csiga
    crn
    cuni
    #
    wcel
    #
    cS
    cc0
    cpnf
    cicc
    co
    #
    vm
    cv
    #
    wf
    #
    c0
    @3
    cfv
    cc0
    wceq
    #
    vx
    cv
    #
    com
    cdom
    wbr
    vy
    @6
    vy
    cv
    #
    wdisj
    wa
    @6
    cuni
    @3
    cfv
    @6
    @7
    @3
    cfv
    vy
    cesum
    wceq
    wi
    #
    vx
    cS
    cpw
    #
    wral
    #
    w3a
    #
    vm
    cab
    #
    cvv
    wcel
    #
    cS
    cmeas
    cfv
    @12
    wceq
    @1
    @12
    @4
    vm
    cab
    #
    wss
    @14
    cvv
    wcel
    #
    @13
    @11
    @4
    vm
    @4
    @5
    @10
    simp1
    ss2abi
    @1
    @2
    cvv
    wcel
    @15
    cc0
    cpnf
    cicc
    ovex
    cS
    @2
    @0
    cvv
    vm
    mapex
    mpan2
    @12
    @14
    cvv
    ssexg
    sylancr
    vs
    cS
    vs
    cv
    #
    @2
    @3
    wf
    #
    @5
    @8
    vx
    @16
    cpw
    #
    wral
    #
    w3a
    #
    vm
    cab
    @12
    @0
    cvv
    cmeas
    @16
    cS
    wceq
    #
    @20
    @11
    vm
    @21
    @17
    @4
    @19
    @10
    @5
    @16
    cS
    @2
    @3
    feq2
    @21
    @8
    vx
    @18
    @9
    @16
    cS
    pweq
    raleqdv
    3anbi13d
    abbidv
    vx
    vy
    vm
    vs
    df-meas
    fvmptg
    mpdan
end
