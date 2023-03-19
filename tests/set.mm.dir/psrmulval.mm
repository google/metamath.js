include "co.mm"
include "cfv.mm"
include "cv.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "crab.mm"
include "cmin.mm"
include "cof.mm"
include "cmpt.mm"
include "cgsu.mm"
include "psrmulfval.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "breq2.mm"
include "rabbidv.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "mpteq12dv.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eqtrd.mm"

theorem psrmulval
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let vh: setvar h
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  assume psrmulr.s: |- S = ( I mPwSer R )
  assume psrmulr.b: |- B = ( Base ` S )
  assume psrmulr.m: |- .x. = ( .r ` R )
  assume psrmulr.t: |- .xb = ( .r ` S )
  assume psrmulr.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume psrmulfval.i: |- ( ph -> F e. B )
  assume psrmulfval.r: |- ( ph -> G e. B )
  assume psrmulval.r: |- ( ph -> X e. D )

  disjoint B k
  disjoint k y
  disjoint D k
  disjoint D y
  disjoint h k
  disjoint h y
  disjoint I h
  disjoint I k
  disjoint I y
  disjoint k ph
  disjoint F k
  disjoint G k
  disjoint .x. k
  disjoint R k
  disjoint X k
  disjoint X y
  disjoint f g
  disjoint f k
  disjoint f x
  disjoint B f
  disjoint g k
  disjoint g x
  disjoint B g
  disjoint k x
  disjoint B x
  disjoint f y
  disjoint D f
  disjoint g y
  disjoint D g
  disjoint x y
  disjoint D x
  disjoint f h
  disjoint I f
  disjoint g h
  disjoint I g
  disjoint h x
  disjoint I x
  disjoint f ph
  disjoint g ph
  disjoint ph x
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint G f
  disjoint G g
  disjoint G x
  disjoint .x. f
  disjoint .x. g
  disjoint .x. x
  disjoint R f
  disjoint R g
  disjoint R x
  disjoint X x
  assert |- ( ph -> ( ( F .xb G ) ` X ) = ( R gsum ( k e. { y e. D | y oR <_ X } |-> ( ( F ` k ) .x. ( G ` ( X oF - k ) ) ) ) ) )

  proof
    wph
    cX
    cF
    cG
    c.xb
    co
    #
    cfv
    cX
    vx
    cD
    cR
    vk
    vy
    cv
    #
    vx
    cv
    #
    cle
    cofr
    #
    wbr
    #
    vy
    cD
    crab
    #
    vk
    cv
    #
    cF
    cfv
    #
    @2
    @6
    cmin
    cof
    #
    co
    #
    cG
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cfv
    #
    cR
    vk
    @1
    cX
    @3
    wbr
    #
    vy
    cD
    crab
    #
    @7
    cX
    @6
    @8
    co
    #
    cG
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wph
    cX
    @0
    @14
    wph
    vk
    vy
    cB
    cD
    cR
    cS
    c.xb
    c.x
    vh
    vx
    cF
    cG
    cI
    psrmulr.s
    psrmulr.b
    psrmulr.m
    psrmulr.t
    psrmulr.d
    psrmulfval.i
    psrmulfval.r
    psrmulfval
    fveq1d
    wph
    cX
    cD
    wcel
    @15
    @22
    wceq
    psrmulval.r
    vx
    cX
    @13
    @22
    cD
    @14
    @2
    cX
    wceq
    #
    @12
    @21
    cR
    cgsu
    @23
    vk
    @5
    @11
    @17
    @20
    @23
    @4
    @16
    vy
    cD
    @2
    cX
    @1
    @3
    breq2
    rabbidv
    @23
    @10
    @19
    @7
    c.x
    @23
    @9
    @18
    cG
    @2
    cX
    @6
    @8
    oveq1
    fveq2d
    oveq2d
    mpteq12dv
    oveq2d
    @14
    eqid
    cR
    @21
    cgsu
    ovex
    fvmpt
    syl
    eqtrd
end
