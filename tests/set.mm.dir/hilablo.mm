include "cva.mm"
include "chil.mm"
include "c0v.mm"
include "c1.mm"
include "cneg.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "ax-hilex.mm"
include "ax-hfvadd.mm"
include "ax-hvass.mm"
include "ax-hv0cl.mm"
include "hvaddid2.mm"
include "cc.mm"
include "wcel.mm"
include "neg1cn.mm"
include "hvmulcl.mm"
include "mpan.mm"
include "wceq.mm"
include "ax-hvcom.mm"
include "mpancom.mm"
include "hvnegid.mm"
include "eqtrd.mm"
include "isgrpoi.mm"
include "cxp.mm"
include "fdmi.mm"
include "isabloi.mm"

theorem hilablo
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- +h e. AbelOp

  proof
    vx
    vy
    cva
    chil
    vx
    vy
    vz
    c0v
    cva
    c1
    cneg
    #
    vx
    cv
    #
    csm
    co
    #
    chil
    ax-hilex
    ax-hfvadd
    @1
    vy
    cv
    #
    vz
    cv
    ax-hvass
    ax-hv0cl
    @1
    hvaddid2
    @0
    cc
    wcel
    @1
    chil
    wcel
    #
    @2
    chil
    wcel
    #
    neg1cn
    @0
    @1
    hvmulcl
    mpan
    #
    @4
    @2
    @1
    cva
    co
    #
    @1
    @2
    cva
    co
    #
    c0v
    @5
    @4
    @7
    @8
    wceq
    @6
    @2
    @1
    ax-hvcom
    mpancom
    @1
    hvnegid
    eqtrd
    isgrpoi
    chil
    chil
    cxp
    chil
    cva
    ax-hfvadd
    fdmi
    @1
    @3
    ax-hvcom
    isabloi
end
