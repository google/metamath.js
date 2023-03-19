include "chil.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "clf.mm"
include "wcel.mm"
include "cc.mm"
include "wf.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cfv.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "wral.mm"
include "0cn.mm"
include "fconst6.mm"
include "wa.mm"
include "hvmulcl.mm"
include "hvaddcl.mm"
include "sylan.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "syl.mm"
include "oveq2d.mm"
include "mul01.mm"
include "sylan9eqr.mm"
include "oveqan12d.mm"
include "00id.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "3impa.mm"
include "rgen3.mm"
include "ellnfn.mm"
include "mpbir2an.mm"

theorem 0lnfn
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ~H X. { 0 } ) e. LinFn

  proof
    chil
    cc0
    csn
    cxp
    #
    clf
    wcel
    chil
    cc
    @0
    wf
    vx
    cv
    #
    vy
    cv
    #
    csm
    co
    #
    vz
    cv
    #
    cva
    co
    #
    @0
    cfv
    #
    @1
    @2
    @0
    cfv
    #
    cmul
    co
    #
    @4
    @0
    cfv
    #
    caddc
    co
    #
    wceq
    #
    vz
    chil
    wral
    vy
    chil
    wral
    vx
    cc
    wral
    chil
    cc0
    cc
    0cn
    fconst6
    @11
    vx
    vy
    vz
    cc
    chil
    chil
    @1
    cc
    wcel
    #
    @2
    chil
    wcel
    #
    @4
    chil
    wcel
    #
    @11
    @12
    @13
    wa
    #
    @14
    wa
    #
    @6
    cc0
    @10
    @16
    @5
    chil
    wcel
    #
    @6
    cc0
    wceq
    @15
    @3
    chil
    wcel
    @14
    @17
    @1
    @2
    hvmulcl
    @3
    @4
    hvaddcl
    sylan
    chil
    cc0
    @5
    c0ex
    fvconst2
    syl
    @16
    @10
    cc0
    cc0
    caddc
    co
    cc0
    @15
    @14
    @8
    cc0
    @9
    cc0
    caddc
    @13
    @12
    @8
    @1
    cc0
    cmul
    co
    cc0
    @13
    @7
    cc0
    @1
    cmul
    chil
    cc0
    @2
    c0ex
    fvconst2
    oveq2d
    @1
    mul01
    sylan9eqr
    chil
    cc0
    @4
    c0ex
    fvconst2
    oveqan12d
    00id
    syl6eq
    eqtr4d
    3impa
    rgen3
    vx
    vy
    vz
    @0
    ellnfn
    mpbir2an
end
