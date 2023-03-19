include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "cmulr.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mplval2.mm"
include "ressmulr.mm"
include "ax-mp.mm"
include "eqtr4i.mm"
include "mplbasss.mm"
include "sseldi.mm"
include "psrmulfval.mm"

theorem mplmul
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let vh: setvar h
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  assume mplmul.p: |- P = ( I mPoly R )
  assume mplmul.b: |- B = ( Base ` P )
  assume mplmul.m: |- .x. = ( .r ` R )
  assume mplmul.t: |- .xb = ( .r ` P )
  assume mplmul.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume mplmul.f: |- ( ph -> F e. B )
  assume mplmul.g: |- ( ph -> G e. B )

  disjoint k x
  disjoint k y
  disjoint D k
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint F k
  disjoint F x
  disjoint G k
  disjoint G x
  disjoint h k
  disjoint h x
  disjoint h y
  disjoint I h
  disjoint I k
  disjoint I x
  disjoint I y
  disjoint k ph
  disjoint ph x
  disjoint .x. k
  disjoint .x. x
  disjoint R k
  disjoint R x
  assert |- ( ph -> ( F .xb G ) = ( k e. D |-> ( R gsum ( x e. { y e. D | y oR <_ k } |-> ( ( F ` x ) .x. ( G ` ( k oF - x ) ) ) ) ) ) )

  proof
    wph
    vx
    vy
    cI
    cR
    cmps
    co
    #
    cbs
    cfv
    #
    cD
    cR
    @0
    c.xb
    c.x
    vh
    vk
    cF
    cG
    cI
    @0
    eqid
    #
    @1
    eqid
    #
    mplmul.m
    c.xb
    cP
    cmulr
    cfv
    #
    @0
    cmulr
    cfv
    #
    mplmul.t
    cB
    cvv
    wcel
    @5
    @4
    wceq
    cB
    cP
    cbs
    cfv
    cvv
    mplmul.b
    cP
    cbs
    fvex
    eqeltri
    cB
    @0
    cP
    @5
    cvv
    cP
    cR
    @0
    cB
    cI
    mplmul.p
    @2
    mplmul.b
    mplval2
    @5
    eqid
    ressmulr
    ax-mp
    eqtr4i
    mplmul.d
    wph
    cB
    @1
    cF
    @1
    cP
    cR
    @0
    cB
    cI
    mplmul.p
    @2
    mplmul.b
    @3
    mplbasss
    #
    mplmul.f
    sseldi
    wph
    cB
    @1
    cG
    @6
    mplmul.g
    sseldi
    psrmulfval
end
