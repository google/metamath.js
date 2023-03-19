include "cfn.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "c0g.mm"
include "eqid.mm"
include "c0.mm"
include "0fin.mm"
include "a1i.mm"
include "wa.mm"
include "cun.mm"
include "unfi.mm"
include "adantl.mm"
include "wss.mm"
include "ssfi.mm"
include "mplsubglem2.mm"
include "mpllsslem.mm"

theorem mpllss
  let wph: wff ph
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let cW: class W
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let cD: class D
  let cX: class X
  let cY: class Y
  let c.x: class .x.
  let c.0: class .0.
  assume mplsubg.s: |- S = ( I mPwSer R )
  assume mplsubg.p: |- P = ( I mPoly R )
  assume mplsubg.u: |- U = ( Base ` P )
  assume mplsubg.i: |- ( ph -> I e. W )
  assume mpllss.r: |- ( ph -> R e. Ring )


  assert |- ( ph -> U e. ( LSubSp ` S ) )

  proof
    wph
    vx
    vy
    cfn
    cS
    cbs
    cfv
    #
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vf
    cn0
    cI
    cmap
    co
    crab
    #
    cR
    cS
    cU
    vf
    vg
    cI
    cW
    cR
    c0g
    cfv
    #
    mplsubg.s
    @0
    eqid
    @2
    eqid
    @1
    eqid
    mplsubg.i
    c0
    cfn
    wcel
    wph
    0fin
    a1i
    vx
    cv
    #
    cfn
    wcel
    #
    vy
    cv
    #
    cfn
    wcel
    #
    wa
    @3
    @5
    cun
    cfn
    wcel
    wph
    @3
    @5
    unfi
    adantl
    @4
    @5
    @3
    wss
    wa
    @6
    wph
    @3
    @5
    ssfi
    adantl
    wph
    cP
    cR
    cS
    cU
    vg
    cI
    cW
    mplsubg.s
    mplsubg.p
    mplsubg.u
    mplsubg.i
    mplsubglem2
    mpllss.r
    mpllsslem
end
