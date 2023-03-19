include "co.mm"
include "wcel.mm"
include "cop.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "csb.mm"
include "wa.mm"
include "cdm.mm"
include "dmmpt2ssx.mm"
include "cfv.mm"
include "elfvdm.mm"
include "df-ov.mm"
include "eleq2s.mm"
include "sseldi.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "opeliunxp2f.mm"
include "sylib.mm"

theorem mpt2xeldm
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let cN: class N
  let cX: class X
  let cY: class Y
  assume mpt2xeldm2.f: |- F = ( x e. C , y e. D |-> R )

  disjoint C x
  disjoint C y
  disjoint x y
  disjoint D y
  disjoint X x
  disjoint Y x
  assert |- ( N e. ( X F Y ) -> ( X e. C /\ Y e. [_ X / x ]_ D ) )

  proof
    cN
    cX
    cY
    cF
    co
    #
    wcel
    #
    cX
    cY
    cop
    #
    vx
    cC
    vx
    cv
    csn
    cD
    cxp
    ciun
    #
    wcel
    cX
    cC
    wcel
    cY
    vx
    cX
    cD
    csb
    #
    wcel
    wa
    @1
    cF
    cdm
    #
    @3
    @2
    vx
    vy
    cC
    cD
    cR
    cF
    mpt2xeldm2.f
    dmmpt2ssx
    @2
    @5
    wcel
    cN
    @2
    cF
    cfv
    @0
    cN
    @2
    cF
    elfvdm
    cX
    cY
    cF
    df-ov
    eleq2s
    sseldi
    vx
    cC
    cD
    cX
    cY
    @4
    vx
    cX
    cD
    nfcsb1v
    vx
    cX
    cD
    csbeq1a
    opeliunxp2f
    sylib
end
