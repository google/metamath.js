include "cc.mm"
include "cv.mm"
include "cc0.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "co.mm"
include "cmpt.mm"
include "cfv.mm"
include "ccnfld.mm"
include "cnm.mm"
include "wcel.mm"
include "wceq.mm"
include "0cn.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "mpan2.mm"
include "subid1.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "mpteq2ia.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cnfldds.mm"
include "nmfval.mm"
include "wtru.mm"
include "cr.mm"
include "wf.mm"
include "absf.mm"
include "a1i.mm"
include "feqmptd.mm"
include "trud.mm"
include "3eqtr4ri.mm"

theorem cnfldnm
  let vx: setvar x


  assert |- abs = ( norm ` CCfld )

  proof
    vx
    cc
    vx
    cv
    #
    cc0
    cabs
    cmin
    ccom
    #
    co
    #
    cmpt
    vx
    cc
    @0
    cabs
    cfv
    #
    cmpt
    #
    ccnfld
    cnm
    cfv
    #
    cabs
    vx
    cc
    @2
    @3
    @0
    cc
    wcel
    #
    @2
    @0
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    @3
    @6
    cc0
    cc
    wcel
    @2
    @8
    wceq
    0cn
    @0
    cc0
    @1
    @1
    eqid
    cnmetdval
    mpan2
    @6
    @7
    @0
    cabs
    @0
    subid1
    fveq2d
    eqtrd
    mpteq2ia
    vx
    @1
    @5
    ccnfld
    cc
    cc0
    @5
    eqid
    cnfldbas
    cnfld0
    cnfldds
    nmfval
    cabs
    @4
    wceq
    wtru
    vx
    cc
    cr
    cabs
    cc
    cr
    cabs
    wf
    wtru
    absf
    a1i
    feqmptd
    trud
    3eqtr4ri
end
