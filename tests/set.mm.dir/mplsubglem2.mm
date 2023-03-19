include "cv.mm"
include "c0g.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cbs.mm"
include "crab.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "eqid.mm"
include "mplbas.mm"
include "wa.mm"
include "wfun.mm"
include "cvv.mm"
include "wb.mm"
include "psrelbasfun.mm"
include "adantl.mm"
include "simpr.mm"
include "fvexd.mm"
include "funisfsupp.mm"
include "syl3anc.mm"
include "rabbidva.mm"
include "syl5eq.mm"

theorem mplsubglem2
  let wph: wff ph
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let vg: setvar g
  let cI: class I
  let cW: class W
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let vf: setvar f
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

  disjoint I g
  disjoint g ph
  disjoint R g
  disjoint S g
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint f g
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint I f
  disjoint g k
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint k y
  disjoint I k
  disjoint n y
  disjoint I n
  disjoint x y
  disjoint I x
  disjoint I y
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint R f
  disjoint R k
  disjoint R x
  disjoint R y
  disjoint S f
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint D n
  disjoint D x
  disjoint D y
  disjoint U x
  disjoint U y
  disjoint X f
  disjoint X g
  disjoint X k
  disjoint X x
  disjoint Y f
  disjoint Y g
  disjoint Y k
  disjoint Y x
  disjoint .x. x
  disjoint W k
  disjoint W y
  disjoint .0. f
  disjoint .0. g
  disjoint .0. k
  assert |- ( ph -> U = { g e. ( Base ` S ) | ( g supp ( 0g ` R ) ) e. Fin } )

  proof
    wph
    cU
    vg
    cv
    #
    cR
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    vg
    cS
    cbs
    cfv
    #
    crab
    @0
    @1
    csupp
    co
    cfn
    wcel
    #
    vg
    @3
    crab
    @3
    cP
    cR
    cS
    cU
    vg
    cI
    @1
    mplsubg.p
    mplsubg.s
    @3
    eqid
    #
    @1
    eqid
    mplsubg.u
    mplbas
    wph
    @2
    @4
    vg
    @3
    wph
    @0
    @3
    wcel
    #
    wa
    #
    @0
    wfun
    #
    @6
    @1
    cvv
    wcel
    @2
    @4
    wb
    @6
    @8
    wph
    @3
    cR
    cS
    cI
    @0
    mplsubg.s
    @5
    psrelbasfun
    adantl
    wph
    @6
    simpr
    @7
    cR
    c0g
    fvexd
    @0
    @3
    cvv
    @1
    funisfsupp
    syl3anc
    rabbidva
    syl5eq
end
