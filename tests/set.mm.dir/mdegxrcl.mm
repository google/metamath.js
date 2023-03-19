include "wcel.mm"
include "cfv.mm"
include "cv.mm"
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
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "eqid.mm"
include "mdegval.mm"
include "wss.mm"
include "crn.mm"
include "imassrn.mm"
include "cvv.mm"
include "wf.mm"
include "mplrcl.mm"
include "tdeglem1.mm"
include "frn.mm"
include "3syl.mm"
include "cr.mm"
include "nn0ssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "syl6ss.mm"
include "syl5ss.mm"
include "supxrcl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem mdegxrcl
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  let cI: class I
  let vx: setvar x
  let vy: setvar y
  assume mdegxrcl.d: |- D = ( I mDeg R )
  assume mdegxrcl.p: |- P = ( I mPoly R )
  assume mdegxrcl.b: |- B = ( Base ` P )


  assert |- ( F e. B -> ( D ` F ) e. RR* )

  proof
    cF
    cB
    wcel
    #
    cF
    cD
    cfv
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
    cF
    cR
    c0g
    cfv
    #
    csupp
    co
    #
    cima
    #
    cxr
    clt
    csup
    #
    cxr
    @1
    cB
    cD
    cP
    cR
    vy
    vx
    cF
    @2
    cI
    @3
    mdegxrcl.d
    mdegxrcl.p
    mdegxrcl.b
    @3
    eqid
    @1
    eqid
    #
    @2
    eqid
    #
    mdegval
    @0
    @5
    cxr
    wss
    @6
    cxr
    wcel
    @0
    @5
    @2
    crn
    #
    cxr
    @2
    @4
    imassrn
    @0
    @9
    cn0
    cxr
    @0
    cI
    cvv
    wcel
    @1
    cn0
    @2
    wf
    @9
    cn0
    wss
    cB
    cP
    cR
    cI
    cF
    mdegxrcl.p
    mdegxrcl.b
    mplrcl
    @1
    vy
    vx
    @2
    cI
    cvv
    @7
    @8
    tdeglem1
    @1
    cn0
    @2
    frn
    3syl
    cn0
    cr
    cxr
    nn0ssre
    ressxr
    sstri
    syl6ss
    syl5ss
    @5
    supxrcl
    syl
    eqeltrd
end
