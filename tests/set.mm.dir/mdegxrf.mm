include "cxr.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "ccnfld.mm"
include "cgsu.mm"
include "cmpt.mm"
include "c0g.mm"
include "csupp.mm"
include "clt.mm"
include "csup.mm"
include "xrltso.mm"
include "supex.mm"
include "eqid.mm"
include "mdegfval.mm"
include "fnmpti.mm"
include "mdegxrcl.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"

theorem mdegxrf
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cI: class I
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vz: setvar z
  assume mdegxrcl.d: |- D = ( I mDeg R )
  assume mdegxrcl.p: |- P = ( I mPoly R )
  assume mdegxrcl.b: |- B = ( Base ` P )


  assert |- D : B --> RR*

  proof
    cB
    cxr
    cD
    wf
    cD
    cB
    wfn
    vf
    cv
    #
    cD
    cfv
    cxr
    wcel
    #
    vf
    cB
    wral
    vz
    cB
    vy
    vx
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vx
    cn0
    cI
    cmap
    co
    crab
    #
    ccnfld
    vy
    cv
    cgsu
    co
    cmpt
    #
    vz
    cv
    cR
    c0g
    cfv
    #
    csupp
    co
    cima
    #
    cxr
    clt
    csup
    cD
    cxr
    @5
    clt
    xrltso
    supex
    @2
    cB
    cD
    cP
    cR
    vz
    vy
    vx
    @3
    cI
    @4
    mdegxrcl.d
    mdegxrcl.p
    mdegxrcl.b
    @4
    eqid
    @2
    eqid
    @3
    eqid
    mdegfval
    fnmpti
    @1
    vf
    cB
    cB
    cD
    cP
    cR
    @0
    cI
    mdegxrcl.d
    mdegxrcl.p
    mdegxrcl.b
    mdegxrcl
    rgen
    vf
    cB
    cxr
    cD
    ffnfv
    mpbir2an
end
