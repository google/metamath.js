include "cxrs.mm"
include "cmgp.mm"
include "cfv.mm"
include "ccmn.mm"
include "wcel.mm"
include "wtru.mm"
include "cxr.mm"
include "cxmu.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "xrsbas.mm"
include "mgpbas.mm"
include "a1i.mm"
include "cplusg.mm"
include "xrsmul.mm"
include "mgpplusg.mm"
include "c1.mm"
include "cv.mm"
include "co.mm"
include "xmulcl.mm"
include "3adant1.mm"
include "w3a.mm"
include "xmulass.mm"
include "adantl.mm"
include "cr.mm"
include "1re.mm"
include "rexr.mm"
include "mp1i.mm"
include "xmulid2.mm"
include "xmulid1.mm"
include "ismndd.mm"
include "xmulcom.mm"
include "iscmnd.mm"
include "trud.mm"

theorem xrsmcmn
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- ( mulGrp ` RR*s ) e. CMnd

  proof
    cxrs
    cmgp
    cfv
    #
    ccmn
    wcel
    wtru
    vx
    vy
    cxr
    cxmu
    @0
    cxr
    @0
    cbs
    cfv
    wceq
    wtru
    cxr
    cxrs
    @0
    @0
    eqid
    #
    xrsbas
    mgpbas
    a1i
    #
    cxmu
    @0
    cplusg
    cfv
    wceq
    wtru
    cxrs
    cxmu
    @0
    @1
    xrsmul
    mgpplusg
    a1i
    #
    wtru
    vx
    vy
    vz
    cxr
    cxmu
    @0
    c1
    @2
    @3
    vx
    cv
    #
    cxr
    wcel
    #
    vy
    cv
    #
    cxr
    wcel
    #
    @4
    @6
    cxmu
    co
    #
    cxr
    wcel
    wtru
    @4
    @6
    xmulcl
    3adant1
    @5
    @7
    vz
    cv
    #
    cxr
    wcel
    w3a
    @8
    @9
    cxmu
    co
    @4
    @6
    @9
    cxmu
    co
    cxmu
    co
    wceq
    wtru
    @4
    @6
    @9
    xmulass
    adantl
    c1
    cr
    wcel
    c1
    cxr
    wcel
    wtru
    1re
    c1
    rexr
    mp1i
    @5
    c1
    @4
    cxmu
    co
    @4
    wceq
    wtru
    @4
    xmulid2
    adantl
    @5
    @4
    c1
    cxmu
    co
    @4
    wceq
    wtru
    @4
    xmulid1
    adantl
    ismndd
    @5
    @7
    @8
    @6
    @4
    cxmu
    co
    wceq
    wtru
    @4
    @6
    xmulcom
    3adant1
    iscmnd
    trud
end
