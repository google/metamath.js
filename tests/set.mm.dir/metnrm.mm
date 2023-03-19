include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wss.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "ccld.mm"
include "wral.mm"
include "cnrm.mm"
include "mopntop.mm"
include "wa.mm"
include "c1.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "c2.mm"
include "cdiv.mm"
include "cbl.mm"
include "ciun.mm"
include "eqid.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3.mm"
include "metnrmlem3.mm"
include "3expia.mm"
include "ralrimivva.mm"
include "isnrm3.mm"
include "sylanbrc.mm"

theorem metnrm
  let cD: class D
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume metnrm.j: |- J = ( MetOpen ` D )


  assert |- ( D e. ( *Met ` X ) -> J e. Nrm )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cJ
    ctop
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cin
    c0
    wceq
    #
    @1
    vz
    cv
    #
    wss
    @2
    vw
    cv
    #
    wss
    @4
    @5
    cin
    c0
    wceq
    w3a
    vw
    cJ
    wrex
    vz
    cJ
    wrex
    #
    wi
    #
    vy
    cJ
    ccld
    cfv
    #
    wral
    vx
    @8
    wral
    cJ
    cnrm
    wcel
    cD
    cJ
    cX
    metnrm.j
    mopntop
    @0
    @7
    vx
    vy
    @8
    @8
    @0
    @1
    @8
    wcel
    #
    @2
    @8
    wcel
    #
    wa
    #
    @3
    @6
    @0
    @11
    @3
    w3a
    vu
    vv
    vz
    vw
    vs
    cD
    @1
    @2
    vs
    @2
    vs
    cv
    #
    c1
    @12
    vu
    cX
    vv
    @1
    vu
    cv
    vv
    cv
    cD
    co
    #
    cmpt
    crn
    cxr
    clt
    cinf
    cmpt
    #
    cfv
    #
    cle
    wbr
    c1
    @15
    cif
    c2
    cdiv
    co
    cD
    cbl
    cfv
    #
    co
    ciun
    #
    @14
    vu
    cX
    vv
    @2
    @13
    cmpt
    crn
    cxr
    clt
    cinf
    cmpt
    #
    cJ
    vt
    @1
    vt
    cv
    #
    c1
    @19
    @18
    cfv
    #
    cle
    wbr
    c1
    @20
    cif
    c2
    cdiv
    co
    @16
    co
    ciun
    #
    cX
    vt
    @14
    eqid
    metnrm.j
    @0
    @11
    @3
    simp1
    @0
    @9
    @10
    @3
    simp2l
    @0
    @9
    @10
    @3
    simp2r
    @0
    @11
    @3
    simp3
    @17
    eqid
    @18
    eqid
    @21
    eqid
    metnrmlem3
    3expia
    ralrimivva
    vz
    vw
    cJ
    vx
    vy
    isnrm3
    sylanbrc
end
