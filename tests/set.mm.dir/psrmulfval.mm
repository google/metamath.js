include "wcel.mm"
include "co.mm"
include "cv.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "crab.mm"
include "cfv.mm"
include "cmin.mm"
include "cof.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "wa.mm"
include "fveq1.mm"
include "oveqan12d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "psrmulr.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "ovex.mm"
include "rabex2.mm"
include "mptex.mm"
include "ovmpt2a.mm"
include "syl2anc.mm"

theorem psrmulfval
  let wph: wff ph
  let vx: setvar x
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
  let vf: setvar f
  let vg: setvar g
  let cX: class X
  assume psrmulr.s: |- S = ( I mPwSer R )
  assume psrmulr.b: |- B = ( Base ` S )
  assume psrmulr.m: |- .x. = ( .r ` R )
  assume psrmulr.t: |- .xb = ( .r ` S )
  assume psrmulr.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume psrmulfval.i: |- ( ph -> F e. B )
  assume psrmulfval.r: |- ( ph -> G e. B )

  disjoint k x
  disjoint B k
  disjoint B x
  disjoint k y
  disjoint D k
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint h k
  disjoint h x
  disjoint h y
  disjoint I h
  disjoint I k
  disjoint I x
  disjoint I y
  disjoint k ph
  disjoint ph x
  disjoint F k
  disjoint F x
  disjoint G k
  disjoint G x
  disjoint .x. k
  disjoint .x. x
  disjoint R k
  disjoint R x
  disjoint f g
  disjoint f k
  disjoint f x
  disjoint B f
  disjoint g k
  disjoint g x
  disjoint B g
  disjoint f y
  disjoint D f
  disjoint g y
  disjoint D g
  disjoint f h
  disjoint I f
  disjoint g h
  disjoint I g
  disjoint f ph
  disjoint g ph
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint .x. f
  disjoint .x. g
  disjoint R f
  disjoint R g
  disjoint X k
  disjoint X x
  disjoint X y
  assert |- ( ph -> ( F .xb G ) = ( k e. D |-> ( R gsum ( x e. { y e. D | y oR <_ k } |-> ( ( F ` x ) .x. ( G ` ( k oF - x ) ) ) ) ) ) )

  proof
    wph
    cF
    cB
    wcel
    cG
    cB
    wcel
    cF
    cG
    c.xb
    co
    vk
    cD
    cR
    vx
    vy
    cv
    vk
    cv
    #
    cle
    cofr
    wbr
    vy
    cD
    crab
    #
    vx
    cv
    #
    cF
    cfv
    #
    @0
    @2
    cmin
    cof
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
    wceq
    psrmulfval.i
    psrmulfval.r
    vf
    vg
    cF
    cG
    cB
    cB
    vk
    cD
    cR
    vx
    @1
    @2
    vf
    cv
    #
    cfv
    #
    @4
    vg
    cv
    #
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
    @9
    c.xb
    @10
    cF
    wceq
    #
    @12
    cG
    wceq
    #
    wa
    #
    vk
    cD
    @16
    @8
    @19
    @15
    @7
    cR
    cgsu
    @19
    vx
    @1
    @14
    @6
    @17
    @18
    @11
    @3
    @13
    @5
    c.x
    @2
    @10
    cF
    fveq1
    @4
    @12
    cG
    fveq1
    oveqan12d
    mpteq2dv
    oveq2d
    mpteq2dv
    vx
    vy
    cB
    cD
    cR
    cS
    c.xb
    c.x
    vf
    vg
    vh
    vk
    cI
    psrmulr.s
    psrmulr.b
    psrmulr.m
    psrmulr.t
    psrmulr.d
    psrmulr
    vk
    cD
    @8
    vh
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vh
    cn0
    cI
    cmap
    co
    cD
    psrmulr.d
    cn0
    cI
    cmap
    ovex
    rabex2
    mptex
    ovmpt2a
    syl2anc
end
