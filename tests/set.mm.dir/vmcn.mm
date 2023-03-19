include "cnv.mm"
include "wcel.mm"
include "cba.mm"
include "cfv.mm"
include "cv.mm"
include "c1.mm"
include "cneg.mm"
include "cns.mm"
include "co.mm"
include "cpv.mm"
include "cmpt2.mm"
include "ctx.mm"
include "ccn.mm"
include "eqid.mm"
include "nvmfval.mm"
include "cxmt.mm"
include "ctopon.mm"
include "imsxmet.mm"
include "mopntopon.mm"
include "syl.mm"
include "cnmpt1st.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cc.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "neg1cn.mm"
include "cnmpt2c.mm"
include "cnmpt2nd.mm"
include "smcn.mm"
include "cnmpt22f.mm"
include "vacn.mm"
include "eqeltrd.mm"

theorem vmcn
  let cC: class C
  let cU: class U
  let cJ: class J
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  assume vmcn.c: |- C = ( IndMet ` U )
  assume vmcn.j: |- J = ( MetOpen ` C )
  assume vmcn.m: |- M = ( -v ` U )


  assert |- ( U e. NrmCVec -> M e. ( ( J tX J ) Cn J ) )

  proof
    cU
    cnv
    wcel
    #
    cM
    vx
    vy
    cU
    cba
    cfv
    #
    @1
    vx
    cv
    #
    c1
    cneg
    #
    vy
    cv
    #
    cU
    cns
    cfv
    #
    co
    #
    cU
    cpv
    cfv
    #
    co
    cmpt2
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    vx
    vy
    @5
    cU
    @7
    cM
    @1
    @1
    eqid
    #
    @7
    eqid
    #
    @5
    eqid
    #
    vmcn.m
    nvmfval
    @0
    vx
    vy
    @2
    @6
    @7
    cJ
    cJ
    cJ
    cJ
    cJ
    @1
    @1
    @0
    cC
    @1
    cxmt
    cfv
    wcel
    cJ
    @1
    ctopon
    cfv
    wcel
    cC
    cU
    @1
    @8
    vmcn.c
    imsxmet
    cC
    cJ
    @1
    vmcn.j
    mopntopon
    syl
    #
    @11
    @0
    vx
    vy
    cJ
    cJ
    @1
    @1
    @11
    @11
    cnmpt1st
    @0
    vx
    vy
    @3
    @4
    @5
    cJ
    cJ
    ccnfld
    ctopn
    cfv
    #
    cJ
    cJ
    @1
    @1
    @11
    @11
    @0
    vx
    vy
    @3
    cJ
    cJ
    @12
    @1
    @1
    cc
    @11
    @11
    @12
    cc
    ctopon
    cfv
    wcel
    @0
    @12
    @12
    eqid
    #
    cnfldtopon
    a1i
    @3
    cc
    wcel
    @0
    neg1cn
    a1i
    cnmpt2c
    @0
    vx
    vy
    cJ
    cJ
    @1
    @1
    @11
    @11
    cnmpt2nd
    cC
    @5
    cU
    cJ
    @12
    vmcn.c
    vmcn.j
    @10
    @13
    smcn
    cnmpt22f
    cC
    cU
    @7
    cJ
    vmcn.c
    vmcn.j
    @9
    vacn
    cnmpt22f
    eqeltrd
end
