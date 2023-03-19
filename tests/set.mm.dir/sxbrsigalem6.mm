include "cz.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "cico.mm"
include "cmpt2.mm"
include "crn.mm"
include "cxp.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "cbvmpt2v.mm"
include "eqid.mm"
include "sxbrsigalem5.mm"

theorem sxbrsigalem6
  let cJ: class J
  let va: setvar a
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )


  assert |- ( sigaGen ` ( J tX J ) ) C_ ( BrSiga sX BrSiga )

  proof
    vx
    vv
    vu
    vu
    vv
    va
    vm
    cz
    cz
    va
    cv
    #
    c2
    vm
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    @0
    c1
    caddc
    co
    #
    @2
    cdiv
    co
    #
    cico
    co
    #
    cmpt2
    #
    crn
    #
    @8
    vu
    cv
    vv
    cv
    cxp
    cmpt2
    #
    vn
    @7
    cJ
    sxbrsiga.0
    va
    vm
    vx
    vn
    cz
    cz
    @6
    vx
    cv
    #
    c2
    vn
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    @10
    c1
    caddc
    co
    #
    @12
    cdiv
    co
    #
    cico
    co
    @10
    @2
    cdiv
    co
    #
    @14
    @2
    cdiv
    co
    #
    cico
    co
    va
    vx
    weq
    #
    @3
    @16
    @5
    @17
    cico
    @0
    @10
    @2
    cdiv
    oveq1
    @18
    @4
    @14
    @2
    cdiv
    @0
    @10
    c1
    caddc
    oveq1
    oveq1d
    oveq12d
    vm
    vn
    weq
    #
    @16
    @13
    @17
    @15
    cico
    @19
    @2
    @12
    @10
    cdiv
    @1
    @11
    c2
    cexp
    oveq2
    #
    oveq2d
    @19
    @2
    @12
    @14
    cdiv
    @20
    oveq2d
    oveq12d
    cbvmpt2v
    @9
    eqid
    sxbrsigalem5
end
