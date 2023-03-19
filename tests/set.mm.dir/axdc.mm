include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "crn.mm"
include "cdm.mm"
include "wss.mm"
include "cfv.mm"
include "csuc.mm"
include "com.mm"
include "wral.mm"
include "wi.mm"
include "cvv.mm"
include "cab.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "wceq.mm"
include "weq.mm"
include "breq2.mm"
include "cbvabv.mm"
include "breq1.mm"
include "abbidv.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "rdgeq1.mm"
include "reseq1.mm"
include "mp2b.mm"
include "axdclem2.mm"
include "exlimiv.mm"
include "imp.mm"

theorem axdc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vn: setvar n
  let vv: setvar v
  let vg: setvar g
  let vu: setvar u
  let vw: setvar w

  disjoint f n
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint f v
  disjoint f g
  disjoint f u
  disjoint f w
  disjoint n v
  disjoint g n
  disjoint n u
  disjoint n w
  disjoint v x
  disjoint g x
  disjoint u x
  disjoint w x
  disjoint v y
  disjoint g y
  disjoint u y
  disjoint w y
  disjoint v z
  disjoint g z
  disjoint u z
  disjoint w z
  disjoint g v
  disjoint u v
  disjoint v w
  disjoint g u
  disjoint g w
  disjoint u w
  assert |- ( ( E. y E. z y x z /\ ran x C_ dom x ) -> E. f A. n e. _om ( f ` n ) x ( f ` suc n ) )

  proof
    vy
    cv
    #
    vz
    cv
    #
    vx
    cv
    #
    wbr
    vz
    wex
    #
    vy
    wex
    @2
    crn
    @2
    cdm
    wss
    #
    vn
    cv
    #
    vf
    cv
    #
    cfv
    @5
    csuc
    @6
    cfv
    @2
    wbr
    vn
    com
    wral
    vf
    wex
    #
    @3
    @4
    @7
    wi
    vy
    vx
    vv
    vz
    vf
    vg
    vn
    vu
    cvv
    vu
    cv
    #
    vw
    cv
    #
    @2
    wbr
    #
    vw
    cab
    #
    vg
    cv
    #
    cfv
    #
    cmpt
    #
    @0
    crdg
    #
    com
    cres
    #
    vy
    @14
    vv
    cvv
    vv
    cv
    #
    @1
    @2
    wbr
    #
    vz
    cab
    #
    @12
    cfv
    #
    cmpt
    #
    wceq
    @15
    @21
    @0
    crdg
    #
    wceq
    @16
    @22
    com
    cres
    wceq
    vu
    vv
    cvv
    @13
    @20
    vu
    vv
    weq
    #
    @11
    @19
    @12
    @23
    @11
    @8
    @1
    @2
    wbr
    #
    vz
    cab
    @19
    @10
    @24
    vw
    vz
    @9
    @1
    @8
    @2
    breq2
    cbvabv
    @23
    @24
    @18
    vz
    @8
    @17
    @1
    @2
    breq1
    abbidv
    syl5eq
    fveq2d
    cbvmptv
    @0
    @14
    @21
    rdgeq1
    @15
    @22
    com
    reseq1
    mp2b
    axdclem2
    exlimiv
    imp
end
